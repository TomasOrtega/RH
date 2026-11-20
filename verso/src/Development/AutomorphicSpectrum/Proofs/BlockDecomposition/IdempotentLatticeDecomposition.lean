import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulEqOfRangeLe
import GroundTheory.AutomorphicForms.AnisotropicHeight

open NumberField IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 GlobalTheory.CompanionTheory.TorusCh
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.TorusCh.Signs

/- English proof (translation)
Use function extensionality and compare the values at `i`. Unfold `sMeet`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `h1 : (Pi.single k y : Fin m → SignType) i = 0` using `Pi.single_eq_of_ne hjk _`.

Rewrite using `[h1, Pi.single_eq_same]`. Apply the tactic sequence `by_cases hx : x = 0 <;> simp [hx]`. Establish `h1 : (Pi.single j x : Fin m → SignType) i = 0` using `Pi.single_eq_of_ne hij _`. Rewrite using `[h1]`. Simplify using the standard rewrite rules.
-/
theorem sMeet_single_single {m : ℕ} {j k : Fin m} (hjk : j ≠ k) (x y : SignType) :
    sMeet (Pi.single j x) (Pi.single k y) = (0 : Fin m → SignType) := by
  funext i
  unfold sMeet
  by_cases hij : i = j
  · subst hij
    have h1 : (Pi.single k y : Fin m → SignType) i = 0 := Pi.single_eq_of_ne hjk _
    rw [h1, Pi.single_eq_same]
    by_cases hx : x = 0 <;> simp [hx]
  · have h1 : (Pi.single j x : Fin m → SignType) i = 0 := Pi.single_eq_of_ne hij _
    rw [h1]
    simp

/- English proof (translation)
Introduce `i hi`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Conclude with `absurd (Pi.single_eq_of_ne hij _) hi`.
-/
theorem sLe_single {m : ℕ} (e : Fin m → SignType) (j : Fin m) : SLe (Pi.single j (e j)) e := by
  intro i hi
  by_cases hij : i = j
  · subst hij
    simp
  · exact absurd (Pi.single_eq_of_ne hij _) hi

/- English proof (translation)
Introduce `i hi`. Establish `h1` using `congrFun h i`. Unfold `sMeet at h1`. Distinguish the cases in `h2 : e i = e' i`. Conclude with `h2.symm`.

Rewrite `h1` using `[if_neg h2]`. Conclude with `absurd h1.symm hi`.
-/
theorem sLe_of_sMeet {m : ℕ} {e e' : Fin m → SignType} (h : sMeet e e' = e) : SLe e e' := by
  intro i hi
  have h1 := congrFun h i
  unfold sMeet at h1
  by_cases h2 : e i = e' i
  · exact h2.symm
  · rw [if_neg h2] at h1
    exact absurd h1.symm hi

/- English proof (translation)
Use `revert x`. Evaluate the decidable proposition.
-/
theorem eq_neg_one_of {x : SignType} : x ≠ 0 → x ≠ 1 → x = -1 := by
  revert x
  decide

variable {R : Type} [CommRing R] (σ : R →+* R) {m : ℕ} (P : (Fin m → SignType) → R)

/- English proof (translation)
Use `set a : Fin m → Fin m → SignType := fun j => Pi.single j (e j) with ha`. Establish `h2 : ∀ j k, j ≠ k → P (a j) * P (a k) = 0`. Introduce `j k hjk`. Rewrite using `[← hmeet, ha]`. Simplify using `only`.

Rewrite using `[sMeet_single_single hjk, hP0]`. Establish `h4 : ∀ j, P (a j) * P e = P (a j)` using `fun j => hle _ _ (sLe_single e j)`. Use `set q : R := ∑ j, P (a j) with hq`. Establish `h5 : ∀ j, P (a j) * q = P (a j)`. Introduce `j`.

Rewrite using `[hq, Finset.mul_sum, Finset.sum_eq_single j (fun k _ hk => h2 j k hk.symm) (fun h => absurd (Finset.mem_univ j) h), hP2]`. Establish `hqq : q * q = q` using `by conv_lhs => rw [hq, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => h5 j`. Establish `hqe : q * P e = q` using `by conv_lhs => rw [hq, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun j _ => h4 j`.

Establish `hPe` using `hP2 e`. Use `set r : R := P e - q with hr`. Establish `hrr : r * r = r`. Rewrite using `[hr]`. Take the linear combination `hPe - 2 * hqe + hqq`.

Establish `hre : r * P e = r`. Rewrite using `[hr]`. Take the linear combination `hPe - hqe`. Establish `hrs : r * σ r = 0`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨e', he'⟩` from `hsurj r hrr hrs`. Establish `hm : sMeet e' e = e'` using `hinj (by rw [hmeet, he', hre])`. Establish `hse : SLe e' e` using `sLe_of_sMeet hm`. Establish `he0 : e' = 0`. Use function extensionality and compare the values at `j`.

Assume the negation of the conclusion as `hne`. Establish `hne' : e' j ≠ 0` using `hne`. Establish `hej : e j = e' j` using `hse j hne'`. Establish `hs : SLe (a j) e'`. Introduce `i hi`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[ha, hej]`. Conclude with `absurd (Pi.single_eq_of_ne hij _) hi`. Establish `h6 : P (a j) * r = P (a j)`.

Rewrite using `[← he']`. Conclude with `hle _ _ hs`. Establish `h7 : P (a j) * r = 0`. Rewrite using `[hr, mul_sub, h4, h5, sub_self]`. Establish `h8 : a j = 0` using `hinj (by rw [hP0, ← h6, h7])`.

Establish `h9` using `congrFun h8 j`. Simplify using `only [ha, Pi.single_eq_same, Pi.zero_apply] at h9`. Conclude with `hne' (hej ▸ h9)`. Establish `hr0 : r = 0` using `by rw [← he', he0, hP0]`. Conclude with `sub_eq_zero.1 hr0`.
-/
theorem additive (hP2 : ∀ e, P e * P e = P e) (hiso : ∀ e, P e * σ (P e) = 0)
    (hsurj : ∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) (hinj : Function.Injective P) (hP0 : P 0 = 0)
    (hmeet : ∀ e e', P (sMeet e e') = P e * P e') (hle : ∀ e e', SLe e e' → P e * P e' = P e)
    (e : Fin m → SignType) : P e = ∑ j, P (Pi.single j (e j)) := by
  set a : Fin m → Fin m → SignType := fun j => Pi.single j (e j) with ha
  have h2 : ∀ j k, j ≠ k → P (a j) * P (a k) = 0 := by
    intro j k hjk
    rw [← hmeet, ha]
    simp only
    rw [sMeet_single_single hjk, hP0]
  have h4 : ∀ j, P (a j) * P e = P (a j) := fun j => hle _ _ (sLe_single e j)
  set q : R := ∑ j, P (a j) with hq
  have h5 : ∀ j, P (a j) * q = P (a j) := by
    intro j
    rw [hq, Finset.mul_sum, Finset.sum_eq_single j (fun k _ hk => h2 j k hk.symm)
      (fun h => absurd (Finset.mem_univ j) h), hP2]
  have hqq : q * q = q := by
    conv_lhs => rw [hq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => h5 j
  have hqe : q * P e = q := by
    conv_lhs => rw [hq, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => h4 j
  have hPe := hP2 e
  set r : R := P e - q with hr
  have hrr : r * r = r := by
    rw [hr]
    linear_combination hPe - 2 * hqe + hqq
  have hre : r * P e = r := by
    rw [hr]
    linear_combination hPe - hqe
  have hrs : r * σ r = 0 := by
    calc r * σ r = (r * P e) * σ (r * P e) := by rw [hre]
      _ = r * σ r * (P e * σ (P e)) := by rw [map_mul]; ring
      _ = 0 := by rw [hiso, mul_zero]
  obtain ⟨e', he'⟩ := hsurj r hrr hrs
  have hm : sMeet e' e = e' := hinj (by rw [hmeet, he', hre])
  have hse : SLe e' e := sLe_of_sMeet hm
  have he0 : e' = 0 := by
    funext j
    by_contra hne
    have hne' : e' j ≠ 0 := hne
    have hej : e j = e' j := hse j hne'
    have hs : SLe (a j) e' := by
      intro i hi
      by_cases hij : i = j
      · subst hij
        simp [ha, hej]
      · exact absurd (Pi.single_eq_of_ne hij _) hi
    have h6 : P (a j) * r = P (a j) := by
      rw [← he']
      exact hle _ _ hs
    have h7 : P (a j) * r = 0 := by
      rw [hr, mul_sub, h4, h5, sub_self]
    have h8 : a j = 0 := hinj (by rw [hP0, ← h6, h7])
    have h9 := congrFun h8 j
    simp only [ha, Pi.single_eq_same, Pi.zero_apply] at h9
    exact hne' (hej ▸ h9)
  have hr0 : r = 0 := by rw [← he', he0, hP0]
  exact sub_eq_zero.1 hr0

/- English proof (translation)
Use `set δ : Fin m → SignType := Pi.single j 1 with hδ`. Establish `hδ0 : δ ≠ 0`. Introduce `h`. Establish `h1` using `congrFun h j`. Simplify using `[hδ] at h1`.

Use `set p : R := P δ with hp`. Use `set s : R := σ p with hs`. Establish `hpp : p * p = p` using `hP2 δ`. Establish `hps : p * s = 0` using `hiso δ`. Establish `hss : s * s = s` using `by rw [hs, ← map_mul, hpp]`.

Establish `hsp : σ s = p` using `hσ p`. Establish `hsσ : s * σ s = 0` using `by rw [hsp, mul_comm, hps]`. Take `⟨e'', he''⟩` from `hsurj s hss hsσ`. Establish `hsupp : ∀ k, k ≠ j → e'' k = 0`. Introduce `k hkj`.

Assume the negation of the conclusion as `hne`. Use `set β : Fin m → SignType := Pi.single k (e'' k) with hβ`. Use `set c : Fin m → SignType := Function.update δ k (e'' k) with hc`. Establish `hδc : SLe δ c`. Introduce `i hi`.

Establish `hik : i ≠ k`. Introduce and unpack `rfl`. Conclude with `hi (Pi.single_eq_of_ne hkj _)`. Conclude with `Function.update_of_ne hik _ _`. Establish `hβc : SLe β c`.

Introduce `i hi`. Distinguish the cases in `hik : i = k`. Substitute `hik` using the available equality. Simplify using `[hβ, hc]`. Conclude with `absurd (Pi.single_eq_of_ne hik _) hi`.

Establish `h1 : p * σ (P β) = 0`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : P β * s = P β`. Rewrite using `[← he'']`. Conclude with `hle _ _ (sLe_single e'' k)`.

Establish `h3 : σ (P β) * p = σ (P β)`. Use `congrArg σ h2` as an intermediate fact. Rewrite `this` using `[map_mul, hsp]`. Then use the resulting hypothesis. Establish `h4 : σ (P β) = 0`. Rewrite using `[← h3, mul_comm, h1]`.

Establish `h5 : P β = 0`. Rewrite using `[← hσ (P β), h4, map_zero]`. Establish `h6 : β = 0` using `hinj (by rw [h5, hP0])`. Establish `h7` using `congrFun h6 k`. Simplify using `only [hβ, Pi.single_eq_same, Pi.zero_apply] at h7`.

Conclude with `hne h7`. Establish `hform : e'' = Pi.single j (e'' j)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Pi.single_eq_of_ne hij, hsupp i hij]`. Establish `hne0 : e'' j ≠ 0`. Introduce `h0`. Establish `h1 : e'' = 0`.

Rewrite using `[hform, h0]`. Simplify using the standard rewrite rules. Establish `h2 : s = 0` using `by rw [← he'', h1, hP0]`. Establish `h3 : p = 0` using `by rw [← hsp, h2, map_zero]`. Conclude with `hδ0 (hinj (by rw [hP0, ← hp, h3]))`.

Establish `hne1 : e'' j ≠ 1`. Introduce `h1`. Establish `h2 : e'' = δ` using `by rw [hform, h1]`. Establish `h3 : s = p` using `by rw [← he'', h2]`. Establish `h4 : p = 0`.

Establish `h5` using `hps`. Rewrite `h5` using `[h3, hpp]`. Then use the resulting hypothesis. Conclude with `hδ0 (hinj (by rw [hP0, ← hp, h4]))`. Establish `hm1` using `eq_neg_one_of hne0 hne1`. Rewrite using `[← hm1, ← hform, he'']`.
-/
theorem conj_single (hσ : ∀ x, σ (σ x) = x) (hP2 : ∀ e, P e * P e = P e) (hiso : ∀ e, P e * σ (P e) = 0)
    (hsurj : ∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) (hinj : Function.Injective P) (hP0 : P 0 = 0)
    (hle : ∀ e e', SLe e e' → P e * P e' = P e) (j : Fin m) :
    P (Pi.single j (-1)) = σ (P (Pi.single j 1)) := by
  set δ : Fin m → SignType := Pi.single j 1 with hδ
  have hδ0 : δ ≠ 0 := by
    intro h
    have h1 := congrFun h j
    simp [hδ] at h1
  set p : R := P δ with hp
  set s : R := σ p with hs
  have hpp : p * p = p := hP2 δ
  have hps : p * s = 0 := hiso δ
  have hss : s * s = s := by rw [hs, ← map_mul, hpp]
  have hsp : σ s = p := hσ p
  have hsσ : s * σ s = 0 := by rw [hsp, mul_comm, hps]
  obtain ⟨e'', he''⟩ := hsurj s hss hsσ
  have hsupp : ∀ k, k ≠ j → e'' k = 0 := by
    intro k hkj
    by_contra hne
    set β : Fin m → SignType := Pi.single k (e'' k) with hβ
    set c : Fin m → SignType := Function.update δ k (e'' k) with hc
    have hδc : SLe δ c := by
      intro i hi
      have hik : i ≠ k := by
        rintro rfl
        exact hi (Pi.single_eq_of_ne hkj _)
      exact Function.update_of_ne hik _ _
    have hβc : SLe β c := by
      intro i hi
      by_cases hik : i = k
      · subst hik
        simp [hβ, hc]
      · exact absurd (Pi.single_eq_of_ne hik _) hi
    have h1 : p * σ (P β) = 0 := by
      calc p * σ (P β) = (p * P c) * σ (P β * P c) := by rw [hp, hle _ _ hδc, hle _ _ hβc]
        _ = p * σ (P β) * (P c * σ (P c)) := by rw [map_mul]; ring
        _ = 0 := by rw [hiso, mul_zero]
    have h2 : P β * s = P β := by
      rw [← he'']
      exact hle _ _ (sLe_single e'' k)
    have h3 : σ (P β) * p = σ (P β) := by
      have := congrArg σ h2
      rwa [map_mul, hsp] at this
    have h4 : σ (P β) = 0 := by
      rw [← h3, mul_comm, h1]
    have h5 : P β = 0 := by
      rw [← hσ (P β), h4, map_zero]
    have h6 : β = 0 := hinj (by rw [h5, hP0])
    have h7 := congrFun h6 k
    simp only [hβ, Pi.single_eq_same, Pi.zero_apply] at h7
    exact hne h7
  have hform : e'' = Pi.single j (e'' j) := by
    funext i
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Pi.single_eq_of_ne hij, hsupp i hij]
  have hne0 : e'' j ≠ 0 := by
    intro h0
    have h1 : e'' = 0 := by
      rw [hform, h0]
      simp
    have h2 : s = 0 := by rw [← he'', h1, hP0]
    have h3 : p = 0 := by rw [← hsp, h2, map_zero]
    exact hδ0 (hinj (by rw [hP0, ← hp, h3]))
  have hne1 : e'' j ≠ 1 := by
    intro h1
    have h2 : e'' = δ := by rw [hform, h1]
    have h3 : s = p := by rw [← he'', h2]
    have h4 : p = 0 := by
      have h5 := hps
      rwa [h3, hpp] at h5
    exact hδ0 (hinj (by rw [hP0, ← hp, h4]))
  have hm1 := eq_neg_one_of hne0 hne1
  rw [← hm1, ← hform, he'']

end GlobalTheory.CompanionTheory.TorusCh.Signs

namespace GlobalTheory.CompanionTheory.TorusCh

/- English proof (translation)
Introduce `R _ hc σ hσ m P hP2 hiso hsurj hinj hP0 hmeet hle`. Use `letI : CommRing R := { (inferInstance : Ring R) with mul_comm := hc }`. Conclude with `⟨fun e => Signs.additive σ P hP2 hiso hsurj hinj hP0 hmeet hle e, fun j => Signs.conj_single σ P hσ hP2 hiso hsurj hinj hP0 hle j⟩`.
-/
theorem isotropicIdempotent_signs : ∀ (R : Type) [Ring R], (∀ x y : R, x * y = y * x) → ∀ (σ : R →+* R), (∀ x, σ (σ x) = x) →
    ∀ (m : ℕ) (P : (Fin m → SignType) → R), (∀ e, P e * P e = P e) → (∀ e, P e * σ (P e) = 0) →
    (∀ p, p * p = p → p * σ p = 0 → ∃ e, P e = p) → Function.Injective P → P 0 = 0 →
    (∀ e e', P (sMeet e e') = P e * P e') → (∀ e e', SLe e e' → P e * P e' = P e) →
    (∀ e, P e = ∑ j, P (Pi.single j (e j))) ∧ ∀ j, P (Pi.single j (-1)) = σ (P (Pi.single j 1)) := by
  intro R _ hc σ hσ m P hP2 hiso hsurj hinj hP0 hmeet hle
  letI : CommRing R := { (inferInstance : Ring R) with mul_comm := hc }
  exact ⟨fun e => Signs.additive σ P hP2 hiso hsurj hinj hP0 hmeet hle e,
    fun j => Signs.conj_single σ P hσ hP2 hiso hsurj hinj hP0 hle j⟩

end GlobalTheory.CompanionTheory.TorusCh
