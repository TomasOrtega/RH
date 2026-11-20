import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

noncomputable section

namespace GradedCech

variable (S : Type) [CommRing S] (N : ℕ)

/- English proof (translation)
Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`. Use `⟨Finsupp.single i 1, ?_, rfl⟩` and prove the remaining obligations. Introduce `j hj`.

Rewrite `hj` using `[Finsupp.support_single _ one_ne_zero, Finset.mem_singleton]`. Substitute `hj` using the available equality. Conclude with `hi` after adjusting the coercions. Consider the case `one => exact ⟨0, by simp, by simp⟩`. Consider the case `mul x y _ _ hx hy`.

Take `⟨a, ha, rfl⟩` from `hx`. Take `⟨b, hb, rfl⟩` from `hy`. Conclude with `⟨a + b, Finsupp.support_add.trans (Finset.union_subset ha hb), by rw [monomial_mul, one_mul]⟩`.
-/
theorem exists_monomial_of_mem_monos {I : Finset (Fin (N + 1))} {s : Poly S N}
    (hs : s ∈ Kleiman.monos (S := S) I) :
    ∃ k : Fin (N + 1) →₀ ℕ, k.support ⊆ I ∧ s = monomial k 1 := by
  classical
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Finsupp.single i 1, ?_, rfl⟩
    intro j hj
    rw [Finsupp.support_single _ one_ne_zero, Finset.mem_singleton] at hj
    subst hj
    exact_mod_cast hi
  | one => exact ⟨0, by simp, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, Finsupp.support_add.trans (Finset.union_subset ha hb), by rw [monomial_mul, one_mul]⟩

/- English proof (translation)
Establish `h` using `IsHomogeneous.prod (R := S) I (fun i => (X i : Poly S N)) (fun _ => 1) (fun i _ => isHomogeneous_X S i)`. Rewrite `h` using `[Finset.sum_const, smul_eq_mul, mul_one]`. Conclude with `h.pow n`.
-/
theorem isHomogeneous_Xprod_pow (I : Finset (Fin (N + 1))) (n : ℕ) :
    (IndefiniteRowSideFullHecke.Kleiman.Xprod S N I ^ n).IsHomogeneous (I.card * n) := by
  have h := IsHomogeneous.prod (R := S) I (fun i => (X i : Poly S N)) (fun _ => 1)
    (fun i _ => isHomogeneous_X S i)
  rw [Finset.sum_const, smul_eq_mul, mul_one] at h
  exact h.pow n

/- English proof (translation)
Take `⟨k, hk, rfl⟩` from `exists_monomial_of_mem_monos S N hs`. Establish `hke : k.degree = e` using `(isHomogeneous_monomial (1 : S) rfl).inj_right he (by rw [Ne, monomial_eq_zero]; exact one_ne_zero)`. Use `set D : Fin (N + 1) →₀ ℕ := ∑ i ∈ I, Finsupp.single i e with hD`. Establish `hkD : k ≤ D`. Introduce `j`.

Rewrite using `[hD, Finsupp.finsetSum_apply]`. Distinguish the cases in `hj : j ∈ I`. Rewrite using `[Finset.sum_eq_single j (fun b _ hb => Finsupp.single_eq_of_ne hb.symm) (fun h => (h hj).elim), Finsupp.single_eq_same, ← hke]`. Conclude with `Finsupp.le_degree j k`. Establish `: k j = 0` using `Finsupp.notMem_support_iff.mp (fun h => hj (hk h))`.

Rewrite using `[this]`. Conclude with `Nat.zero_le _`. Establish `hprod : IndefiniteRowSideFullHecke.Kleiman.Xprod S N I ^ e = monomial D 1`. Rewrite using `[IndefiniteRowSideFullHecke.Kleiman.Xprod, ← Finset.prod_pow, hD, monomial_sum_one]`. Conclude with `Finset.prod_congr rfl fun i _ => X_pow_eq_monomial`.

Establish `hst : monomial k (1 : S) * monomial (D - k) 1 = IndefiniteRowSideFullHecke.Kleiman.Xprod S N I ^ e`. Rewrite using `[monomial_mul, one_mul, add_tsub_cancel_of_le hkD, hprod]`. Use `⟨e, monomial (D - k) 1, (D - k).degree, isHomogeneous_monomial 1 rfl, ?_, hst⟩` and prove the remaining obligations. Establish `h1` using `(he.mul (isHomogeneous_monomial (1 : S) (d := D - k) rfl))`. Rewrite `h1` using `[hst]`.

Use `h1.inj_right (isHomogeneous_Xprod_pow S N I e) ?_` and prove the remaining obligations. Rewrite using `[hprod, Ne, monomial_eq_zero]`. Conclude with `one_ne_zero`.
-/
theorem exists_mul_eq_Xprod_pow [Nontrivial S] {I : Finset (Fin (N + 1))} {s : Poly S N}
    (hs : s ∈ Kleiman.monos (S := S) I) {e : ℕ} (he : s.IsHomogeneous e) :
    ∃ (n : ℕ) (t : Poly S N) (d : ℕ), t.IsHomogeneous d ∧ e + d = I.card * n ∧
      s * t = IndefiniteRowSideFullHecke.Kleiman.Xprod S N I ^ n := by
  classical
  obtain ⟨k, hk, rfl⟩ := exists_monomial_of_mem_monos S N hs
  have hke : k.degree = e :=
    (isHomogeneous_monomial (1 : S) rfl).inj_right he (by rw [Ne, monomial_eq_zero]; exact one_ne_zero)
  set D : Fin (N + 1) →₀ ℕ := ∑ i ∈ I, Finsupp.single i e with hD
  have hkD : k ≤ D := by
    intro j
    rw [hD, Finsupp.finsetSum_apply]
    by_cases hj : j ∈ I
    · rw [Finset.sum_eq_single j (fun b _ hb => Finsupp.single_eq_of_ne hb.symm) (fun h => (h hj).elim),
        Finsupp.single_eq_same, ← hke]
      exact Finsupp.le_degree j k
    · have : k j = 0 := Finsupp.notMem_support_iff.mp (fun h => hj (hk h))
      rw [this]
      exact Nat.zero_le _
  have hprod : IndefiniteRowSideFullHecke.Kleiman.Xprod S N I ^ e = monomial D 1 := by
    rw [IndefiniteRowSideFullHecke.Kleiman.Xprod, ← Finset.prod_pow, hD, monomial_sum_one]
    exact Finset.prod_congr rfl fun i _ => X_pow_eq_monomial
  have hst : monomial k (1 : S) * monomial (D - k) 1 = IndefiniteRowSideFullHecke.Kleiman.Xprod S N I ^ e := by
    rw [monomial_mul, one_mul, add_tsub_cancel_of_le hkD, hprod]
  refine ⟨e, monomial (D - k) 1, (D - k).degree, isHomogeneous_monomial 1 rfl, ?_, hst⟩
  have h1 := (he.mul (isHomogeneous_monomial (1 : S) (d := D - k) rfl))
  rw [hst] at h1
  refine h1.inj_right (isHomogeneous_Xprod_pow S N I e) ?_
  rw [hprod, Ne, monomial_eq_zero]
  exact one_ne_zero

variable (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]

def locEquiv (I : Finset (Fin (N + 1))) : IndefiniteRowSideFullHecke.Kleiman.LocM S N M I ≃ₗ[S] Kleiman.LocMod S N M I where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' a x := (algebraMap_smul (Poly S N) a x).symm
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Establish `key : (IndefiniteRowSideFullHecke.Kleiman.locPiece S N M G I.1 c).map (locEquiv S N M I.1 : _ →ₗ[S] _) = Kleiman.degLoc (gradedEquiv S N M G) c I`. Rewrite using `[IndefiniteRowSideFullHecke.Kleiman.locPiece, Submodule.map_span, Kleiman.degLoc]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨n, m, hm, rfl⟩, rfl⟩`.

Use `Submodule.subset_span ⟨m, ⟨IndefiniteRowSideFullHecke.Kleiman.Xprod S N I.1 ^ n, pow_mem (IndefiniteRowSideFullHecke.Kleiman.Xprod_mem_denoms S N I.1) n⟩, c + n * I.1.card, I.1.card * n, hm, isHomogeneous_Xprod_pow S N I.1 n, by push_cast; ring, rfl⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨m, s, a, e, hm, hs, hae, rfl⟩`. Break down `subsingleton_or_nontrivial S with hS | hS` into its components or cases. Establish `hP : Subsingleton (Poly S N)` using `⟨fun p q => MvPolynomial.ext _ _ fun _ => Subsingleton.elim _ _⟩`.

Establish `hm0 : m = 0`. Rewrite using `[← one_smul (Poly S N) m, Subsingleton.elim (1 : Poly S N) 0, zero_smul]`. Substitute `hm0` using the available equality. Rewrite using `[LocalizedModule.zero_mk]`. Conclude with `zero_mem _`.

Take `⟨n, t, d, ht, hed, hst⟩` from `exists_mul_eq_Xprod_pow S N s.2 hs`. Establish `hdeg : a + (d : ℤ) = c + (n : ℤ) * (I.1.card : ℤ)`. Establish `h` using `congrArg (Nat.cast (R := ℤ)) hed`. Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `htm : t • m ∈ G.piece (c + n * I.1.card)`. Rewrite using `[← hdeg]`. Conclude with `(gradedEquiv S N M G).smul_mem d a t m ht hm`. Use `Submodule.subset_span ⟨IndefiniteRowSideFullHecke.Kleiman.locFrac S N M I.1 (t • m) n, ⟨n, t • m, htm, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(LocalizedModule.mk (t • m) ⟨IndefiniteRowSideFullHecke.Kleiman.Xprod S N I.1 ^ n, pow_mem (IndefiniteRowSideFullHecke.Kleiman.Xprod_mem_denoms S N I.1) n⟩ : LocalizedModule (Kleiman.monos (S := S) I.1) M) = LocalizedModule.mk m s`.

Use `LocalizedModule.mk_eq.2 ⟨1, ?_⟩` and prove the remaining obligations. Simplify using `only [one_smul, Submonoid.smul_def]`. Rewrite using `[← mul_smul, hst]`. Rewrite using `[← key, Submodule.mem_map_equiv]`. Both sides reduce to the same expression.
-/
theorem mem_locPiece_iff (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (I : Kleiman.StdCell N)
    (x : IndefiniteRowSideFullHecke.Kleiman.LocM S N M I.1) :
    x ∈ IndefiniteRowSideFullHecke.Kleiman.locPiece S N M G I.1 c ↔
      locEquiv S N M I.1 x ∈ Kleiman.degLoc (gradedEquiv S N M G) c I := by
  have key : (IndefiniteRowSideFullHecke.Kleiman.locPiece S N M G I.1 c).map (locEquiv S N M I.1 : _ →ₗ[S] _) =
      Kleiman.degLoc (gradedEquiv S N M G) c I := by
    rw [IndefiniteRowSideFullHecke.Kleiman.locPiece, Submodule.map_span, Kleiman.degLoc]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨_, ⟨n, m, hm, rfl⟩, rfl⟩
      refine Submodule.subset_span ⟨m, ⟨IndefiniteRowSideFullHecke.Kleiman.Xprod S N I.1 ^ n,
        pow_mem (IndefiniteRowSideFullHecke.Kleiman.Xprod_mem_denoms S N I.1) n⟩, c + n * I.1.card, I.1.card * n, hm,
        isHomogeneous_Xprod_pow S N I.1 n, by push_cast; ring, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
      rcases subsingleton_or_nontrivial S with hS | hS
      · have hP : Subsingleton (Poly S N) :=
          ⟨fun p q => MvPolynomial.ext _ _ fun _ => Subsingleton.elim _ _⟩
        have hm0 : m = 0 := by
          rw [← one_smul (Poly S N) m, Subsingleton.elim (1 : Poly S N) 0, zero_smul]
        subst hm0
        rw [LocalizedModule.zero_mk]
        exact zero_mem _
      · obtain ⟨n, t, d, ht, hed, hst⟩ := exists_mul_eq_Xprod_pow S N s.2 hs
        have hdeg : a + (d : ℤ) = c + (n : ℤ) * (I.1.card : ℤ) := by
          have h := congrArg (Nat.cast (R := ℤ)) hed
          push_cast at h
          linarith
        have htm : t • m ∈ G.piece (c + n * I.1.card) := by
          rw [← hdeg]
          exact (gradedEquiv S N M G).smul_mem d a t m ht hm
        refine Submodule.subset_span ⟨IndefiniteRowSideFullHecke.Kleiman.locFrac S N M I.1 (t • m) n, ⟨n, t • m, htm, rfl⟩, ?_⟩
        change (LocalizedModule.mk (t • m) ⟨IndefiniteRowSideFullHecke.Kleiman.Xprod S N I.1 ^ n,
          pow_mem (IndefiniteRowSideFullHecke.Kleiman.Xprod_mem_denoms S N I.1) n⟩ : LocalizedModule (Kleiman.monos (S := S) I.1) M) =
          LocalizedModule.mk m s
        refine LocalizedModule.mk_eq.2 ⟨1, ?_⟩
        simp only [one_smul, Submonoid.smul_def]
        rw [← mul_smul, hst]
  rw [← key, Submodule.mem_map_equiv]
  rfl

/- English proof (translation)
Simplify using `only [IndefiniteRowSideFullHecke.Kleiman.cechD, LinearMap.pi_apply, if_pos h, LinearMap.sum_apply]`. Both sides reduce to the same expression.
-/
theorem cechD_apply_pos {ι k : Type} [CommRing k] [LinearOrder ι] (C : IndefiniteRowSideFullHecke.Kleiman.CechSystem ι k)
    (v : ∀ I, C.V I) (J : Finset ι) (h : C.good J) :
    IndefiniteRowSideFullHecke.Kleiman.cechD C v J =
      ∑ j ∈ J, IndefiniteRowSideFullHecke.Kleiman.cechSign J j • C.res (Finset.erase_subset j J) (v (J.erase j)) := by
  simp only [IndefiniteRowSideFullHecke.Kleiman.cechD, LinearMap.pi_apply, if_pos h, LinearMap.sum_apply]
  rfl

/- English proof (translation)
Simplify using `only [IndefiniteRowSideFullHecke.Kleiman.cechD, LinearMap.pi_apply, if_neg h]`. Both sides reduce to the same expression.
-/
theorem cechD_apply_neg {ι k : Type} [CommRing k] [LinearOrder ι] (C : IndefiniteRowSideFullHecke.Kleiman.CechSystem ι k)
    (v : ∀ I, C.V I) (J : Finset ι) (h : ¬ C.good J) : IndefiniteRowSideFullHecke.Kleiman.cechD C v J = 0 := by
  simp only [IndefiniteRowSideFullHecke.Kleiman.cechD, LinearMap.pi_apply, if_neg h]
  rfl

variable {S N M}

def extC (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (i : ℕ) :
    Kleiman.Cech.Cochain (Kleiman.locSys S N M) i →ₗ[S] (∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) :=
  LinearMap.pi fun I => if h : I.Nonempty ∧ I.card = i + 1 then
      (locEquiv S N M I).symm.toLinearMap ∘ₗ
        LinearMap.proj (R := S) (φ := fun J : Kleiman.Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i =>
          Kleiman.LocMod S N M J.1.1) ⟨⟨I, h.1, Finset.subset_univ I⟩, h.2⟩
    else 0

def resC (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (i : ℕ) :
    (∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) →ₗ[S] Kleiman.Cech.Cochain (Kleiman.locSys S N M) i :=
  LinearMap.pi fun J => (locEquiv S N M J.1.1).toLinearMap ∘ₗ LinearMap.proj J.1.1

variable (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ)

/- English proof (translation)
Simplify using `only [extC, LinearMap.pi_apply, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem extC_apply_pos {i : ℕ} (v : Kleiman.Cech.Cochain (Kleiman.locSys S N M) i)
    (I : Finset (Fin (N + 1))) (h : I.Nonempty ∧ I.card = i + 1) :
    extC G c i v I = (locEquiv S N M I).symm (v ⟨⟨I, h.1, Finset.subset_univ I⟩, h.2⟩) := by
  simp only [extC, LinearMap.pi_apply, dif_pos h]
  rfl

/- English proof (translation)
Simplify using `only [extC, LinearMap.pi_apply, dif_neg h]`. Both sides reduce to the same expression.
-/
theorem extC_apply_neg {i : ℕ} (v : Kleiman.Cech.Cochain (Kleiman.locSys S N M) i)
    (I : Finset (Fin (N + 1))) (h : ¬ (I.Nonempty ∧ I.card = i + 1)) : extC G c i v I = 0 := by
  simp only [extC, LinearMap.pi_apply, dif_neg h]
  rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem resC_apply {i : ℕ} (w : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I)
    (J : Kleiman.Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) :
    resC G c i w J = locEquiv S N M J.1.1 (w J.1.1) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `J`. Rewrite using `[resC_apply G c, extC_apply_pos G c v J.1.1 ⟨J.1.2.1, J.2⟩]`. Both sides reduce to the same expression.
-/
theorem resC_extC {i : ℕ} (v : Kleiman.Cech.Cochain (Kleiman.locSys S N M) i) :
    resC G c i (extC G c i v) = v := by
  funext J
  rw [resC_apply G c, extC_apply_pos G c v J.1.1 ⟨J.1.2.1, J.2⟩]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hw I`. Establish `hI` using `hw I (Set.mem_univ I)`. Use `beta_reduce at hI`. Use `split_ifs at hI with h`.

Conclude with `⟨fun _ => hI, fun h' => (h' h).elim⟩`. Conclude with `⟨fun h' => (h h').elim, fun _ => (Submodule.mem_bot S).1 hI⟩`. Introduce `hw`. Rewrite using `[IndefiniteRowSideFullHecke.Kleiman.cechC, Submodule.mem_pi]`. Introduce `I _`.

Use `split_ifs with h`. Conclude with `(hw I).1 h`. Conclude with `(Submodule.mem_bot S).2 ((hw I).2 h)`.
-/
theorem mem_cechC_iff {i : ℕ} (w : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) :
    w ∈ IndefiniteRowSideFullHecke.Kleiman.cechC (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i ↔
      ∀ I, (I.Nonempty ∧ I.card = i + 1 → w I ∈ (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).piece I) ∧
        (¬ (I.Nonempty ∧ I.card = i + 1) → w I = 0) := by
  constructor
  · intro hw I
    have hI := hw I (Set.mem_univ I)
    beta_reduce at hI
    split_ifs at hI with h
    · exact ⟨fun _ => hI, fun h' => (h' h).elim⟩
    · exact ⟨fun h' => (h h').elim, fun _ => (Submodule.mem_bot S).1 hI⟩
  · intro hw
    rw [IndefiniteRowSideFullHecke.Kleiman.cechC, Submodule.mem_pi]
    intro I _
    split_ifs with h
    · exact (hw I).1 h
    · exact (Submodule.mem_bot S).2 ((hw I).2 h)

/- English proof (translation)
Use function extensionality and compare the values at `I`. Distinguish the cases in `h : I.Nonempty ∧ I.card = i + 1`. Rewrite using `[extC_apply_pos G c _ I h]`. Both sides reduce to the same expression. Rewrite using `[extC_apply_neg G c _ I h, (((mem_cechC_iff G c w).1 hw I).2 h)]`.
-/
theorem extC_resC {i : ℕ} (w : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I)
    (hw : w ∈ IndefiniteRowSideFullHecke.Kleiman.cechC (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i) :
    extC G c i (resC G c i w) = w := by
  funext I
  by_cases h : I.Nonempty ∧ I.card = i + 1
  · rw [extC_apply_pos G c _ I h]
    rfl
  · rw [extC_apply_neg G c _ I h, (((mem_cechC_iff G c w).1 hw I).2 h)]

/- English proof (translation)
Rewrite using `[mem_cechC_iff]`. Introduce `I`. Use `⟨fun h => ?_, fun h => extC_apply_neg G c v I h⟩` and prove the remaining obligations. Rewrite using `[extC_apply_pos G c v I h]`. Conclude with `(mem_locPiece_iff S N M G c ⟨I, h.1, Finset.subset_univ I⟩ _).2 (hv ⟨⟨I, h.1, Finset.subset_univ I⟩, h.2⟩ (Set.mem_univ _))`.
-/
theorem extC_mem {i : ℕ} (v : Kleiman.Cech.Cochain (Kleiman.locSys S N M) i)
    (hv : v ∈ Kleiman.Cech.Cdeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c) i) :
    extC G c i v ∈ IndefiniteRowSideFullHecke.Kleiman.cechC (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i := by
  rw [mem_cechC_iff]
  intro I
  refine ⟨fun h => ?_, fun h => extC_apply_neg G c v I h⟩
  rw [extC_apply_pos G c v I h]
  exact (mem_locPiece_iff S N M G c ⟨I, h.1, Finset.subset_univ I⟩ _).2
    (hv ⟨⟨I, h.1, Finset.subset_univ I⟩, h.2⟩ (Set.mem_univ _))

/- English proof (translation)
Introduce `J _` and use `(mem_locPiece_iff S N M G c J.1 _).1 (((mem_cechC_iff G c w).1 hw J.1.1).1 ⟨J.1.2.1, J.2⟩)`.
-/
theorem resC_mem {i : ℕ} (w : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I)
    (hw : w ∈ IndefiniteRowSideFullHecke.Kleiman.cechC (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i) :
    resC G c i w ∈ Kleiman.Cech.Cdeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c) i :=
  fun J _ => (mem_locPiece_iff S N M G c J.1 _).1 (((mem_cechC_iff G c w).1 hw J.1.1).1 ⟨J.1.2.1, J.2⟩)

/- English proof (translation)
Use function extensionality and compare the values at `J`. Distinguish the cases in `hJ : J.Nonempty`. Establish `hg : (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).good J` using `hJ`. Use `(cechD_apply_pos _ _ J hg).trans ?_` and prove the remaining obligations. Distinguish the cases in `hc : J.card = i + 1 + 1`.

Rewrite using `[extC_apply_pos G c _ J ⟨hJ, hc⟩, Kleiman.Cech.d_apply, map_sum, ← Finset.sum_coe_sort J]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hj : (J.erase j).Nonempty ∧ (J.erase j).card = i + 1`. Rewrite using `[Finset.card_erase_of_mem j.2, hc]`. Use `⟨Finset.card_pos.mp ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[Finset.card_erase_of_mem j.2, hc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[extC_apply_pos G c _ _ hj, map_zsmul]`. Both sides reduce to the same expression. Rewrite using `[extC_apply_neg G c _ J (fun h => hc h.2)]`.

Use `Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations. Establish `hne : ¬ ((J.erase j).Nonempty ∧ (J.erase j).card = i + 1)`. Introduce and unpack `⟨-, h⟩`. Establish `h1` using `Finset.card_erase_of_mem hj`. Establish `h2` using `Finset.card_pos.mpr hJ`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[extC_apply_neg G c _ _ hne, map_zero, smul_zero]`. Establish `hg : ¬ (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).good J` using `hJ`. Rewrite using `[cechD_apply_neg _ _ J hg, extC_apply_neg G c _ J (fun h => hJ h.1)]`.
-/
theorem cechD_extC {i : ℕ} (v : Kleiman.Cech.Cochain (Kleiman.locSys S N M) i) :
    IndefiniteRowSideFullHecke.Kleiman.cechD (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) (extC G c i v) =
      extC G c (i + 1) (Kleiman.Cech.d (Kleiman.locSys S N M) Kleiman.locResS i v) := by
  funext J
  by_cases hJ : J.Nonempty
  · have hg : (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).good J := hJ
    refine (cechD_apply_pos _ _ J hg).trans ?_
    by_cases hc : J.card = i + 1 + 1
    · rw [extC_apply_pos G c _ J ⟨hJ, hc⟩, Kleiman.Cech.d_apply, map_sum, ← Finset.sum_coe_sort J]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hj : (J.erase j).Nonempty ∧ (J.erase j).card = i + 1 := by
        rw [Finset.card_erase_of_mem j.2, hc]
        refine ⟨Finset.card_pos.mp ?_, rfl⟩
        rw [Finset.card_erase_of_mem j.2, hc]
        omega
      rw [extC_apply_pos G c _ _ hj, map_zsmul]
      rfl
    · rw [extC_apply_neg G c _ J (fun h => hc h.2)]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hne : ¬ ((J.erase j).Nonempty ∧ (J.erase j).card = i + 1) := by
        rintro ⟨-, h⟩
        have h1 := Finset.card_erase_of_mem hj
        have h2 := Finset.card_pos.mpr hJ
        omega
      rw [extC_apply_neg G c _ _ hne, map_zero, smul_zero]
  · have hg : ¬ (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).good J := hJ
    rw [cechD_apply_neg _ _ J hg, extC_apply_neg G c _ J (fun h => hJ h.1)]

def zEquiv (i : ℕ) :
    IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G i c ≃ₗ[S]
      Kleiman.Cech.cocyDeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c)
        Kleiman.locResS i where
  toFun w := ⟨resC G c i w.1, by
    refine ⟨LinearMap.mem_ker.2 ?_, resC_mem G c w.1 w.2.1⟩
    have h := cechD_extC G c (resC G c i w.1)
    rw [extC_resC G c w.1 w.2.1, LinearMap.mem_ker.mp w.2.2] at h
    have h' := congrArg (resC G c (i + 1)) h
    rw [resC_extC G c, map_zero] at h'
    exact h'.symm⟩
  invFun v := ⟨extC G c i v.1, extC_mem G c v.1 v.2.2,
    LinearMap.mem_ker.2 (by rw [cechD_extC G c, LinearMap.mem_ker.mp v.2.1, map_zero])⟩
  map_add' x y := Subtype.ext (map_add (resC G c i) x.1 y.1)
  map_smul' a x := Subtype.ext (map_smul (resC G c i) a x.1)
  left_inv w := Subtype.ext (extC_resC G c w.1 w.2.1)
  right_inv v := Subtype.ext (resC_extC G c v.1)

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]`. Express the relevant statement in the definitionally equal form `extC G c i y.1 ∈ IndefiniteRowSideFullHecke.Kleiman.cechB (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i ↔ y.1 ∈ Kleiman.Cech.bdryDeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c) Kleiman.locResS i`. Consider the cases of `i with`. Consider the case `zero`.

Simplify using `only [IndefiniteRowSideFullHecke.Kleiman.cechB, Kleiman.Cech.bdryDeg, Submodule.mem_bot]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h'` using `congrArg (resC G c 0) h`. Rewrite `h'` using `[resC_extC G c, map_zero]`. Then use the resulting hypothesis.

Introduce `h`. Rewrite using `[h, map_zero]`. Consider the case `succ i`. Simplify using `only [IndefiniteRowSideFullHecke.Kleiman.cechB, Kleiman.Cech.bdryDeg, Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, hw, hwy⟩`. Use `⟨resC G c i w, resC_mem G c w hw, ?_⟩` and prove the remaining obligations. Establish `h` using `cechD_extC G c (resC G c i w)`. Rewrite `h` using `[extC_resC G c w hw, hwy]`. Establish `h'` using `congrArg (resC G c (i + 1)) h`.

Rewrite `h'` using `[resC_extC G c, resC_extC]`. Conclude with `h'.symm`. Introduce and unpack `⟨t, ht, hty⟩`. Conclude with `⟨extC G c i t, extC_mem G c t ht, by rw [cechD_extC G c, hty]⟩`.
-/
theorem zEquiv_map_bdry (i : ℕ) :
    ((IndefiniteRowSideFullHecke.Kleiman.cechB (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i).comap
        (IndefiniteRowSideFullHecke.Kleiman.cechZ (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i).subtype).map
        (zEquiv G c i : IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G i c →ₗ[S] _) =
      (Kleiman.Cech.bdryDeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c)
        Kleiman.locResS i).comap
        (Kleiman.Cech.cocyDeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c)
          Kleiman.locResS i).subtype := by
  ext y
  rw [Submodule.mem_map_equiv, Submodule.mem_comap, Submodule.mem_comap]
  change extC G c i y.1 ∈ IndefiniteRowSideFullHecke.Kleiman.cechB (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c) i ↔
    y.1 ∈ Kleiman.Cech.bdryDeg (Kleiman.locSys S N M) (Kleiman.degLoc (gradedEquiv S N M G) c)
      Kleiman.locResS i
  cases i with
  | zero =>
    simp only [IndefiniteRowSideFullHecke.Kleiman.cechB, Kleiman.Cech.bdryDeg, Submodule.mem_bot]
    constructor
    · intro h
      have h' := congrArg (resC G c 0) h
      rwa [resC_extC G c, map_zero] at h'
    · intro h
      rw [h, map_zero]
  | succ i =>
    simp only [IndefiniteRowSideFullHecke.Kleiman.cechB, Kleiman.Cech.bdryDeg, Submodule.mem_map]
    constructor
    · rintro ⟨w, hw, hwy⟩
      refine ⟨resC G c i w, resC_mem G c w hw, ?_⟩
      have h := cechD_extC G c (resC G c i w)
      rw [extC_resC G c w hw, hwy] at h
      have h' := congrArg (resC G c (i + 1)) h
      rw [resC_extC G c, resC_extC] at h'
      exact h'.symm
    · rintro ⟨t, ht, hty⟩
      exact ⟨extC G c i t, extC_mem G c t ht, by rw [cechD_extC G c, hty]⟩

def hEquiv (i : ℕ) :
    IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c ≃ₗ[S] Kleiman.cohom (gradedEquiv S N M G) i c :=
  Submodule.Quotient.equiv _ _ (zEquiv G c i) (zEquiv_map_bdry G c i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hEquiv_mk (i : ℕ) (w : IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G i c) :
    hEquiv G c i (Submodule.Quotient.mk w) = Submodule.Quotient.mk (zEquiv G c i w) := rfl

end GradedCech

open GradedCech in

/- English proof (translation)
Introduce `S _ N`. Use `⟨fun M _ _ _ _ G i c => hEquiv G c i, ?_, ?_⟩` and prove the remaining obligations. Introduce `M M' _ _ _ _ _ _ _ _ G G' f hf i c z`. Proceed by induction on `z using Submodule.Quotient.induction_on with`. Consider the case `H w`.

Rewrite using `[hEquiv_mk]`. Express the relevant statement in the definitionally equal form `hEquiv G' c i (Submodule.Quotient.mk ((IndefiniteRowSideFullHecke.Kleiman.gradedHom S N hf c).Zmap i w)) = Submodule.Quotient.mk _`. Rewrite using `[hEquiv_mk]`. Use `congr 1`. Introduce `M _ _ _ _ G c m hm z hz`.

Rewrite using `[hEquiv_mk]`. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk _ = Submodule.Quotient.mk _`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `J`.

Express the relevant statement in the definitionally equal form `locEquiv S N M J.1.1 (z.1 J.1.1) = (LocalizedModule.mk m 1 : LocalizedModule (Kleiman.monos (S := S) J.1.1) M)`. Rewrite using `[hz, IndefiniteRowSideFullHecke.Kleiman.unitCochain, if_pos (show J.1.1.card = 1 from J.2)]`. Express the relevant statement in the definitionally equal form `(LocalizedModule.mk m ⟨IndefiniteRowSideFullHecke.Kleiman.Xprod S N J.1.1 ^ 0, _⟩ : LocalizedModule (Kleiman.monos (S := S) J.1.1) M) = LocalizedModule.mk m 1`. Use `congr 1`.
-/
theorem GradedCech.proof : GradedCech.Statement := by
  intro S _ N
  refine ⟨fun M _ _ _ _ G i c => hEquiv G c i, ?_, ?_⟩
  · intro M M' _ _ _ _ _ _ _ _ G G' f hf i c z
    induction z using Submodule.Quotient.induction_on with
    | H w =>
      rw [hEquiv_mk]
      change hEquiv G' c i (Submodule.Quotient.mk ((IndefiniteRowSideFullHecke.Kleiman.gradedHom S N hf c).Zmap i w)) =
        Submodule.Quotient.mk _
      rw [hEquiv_mk]
      congr 1
  · intro M _ _ _ _ G c m hm z hz
    rw [hEquiv_mk]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext J
    change locEquiv S N M J.1.1 (z.1 J.1.1) =
      (LocalizedModule.mk m 1 : LocalizedModule (Kleiman.monos (S := S) J.1.1) M)
    rw [hz, IndefiniteRowSideFullHecke.Kleiman.unitCochain, if_pos (show J.1.1.card = 1 from J.2)]
    change (LocalizedModule.mk m ⟨IndefiniteRowSideFullHecke.Kleiman.Xprod S N J.1.1 ^ 0, _⟩ :
      LocalizedModule (Kleiman.monos (S := S) J.1.1) M) = LocalizedModule.mk m 1
    congr 1

end

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
