import Formalism.CyclotomicNorms.StatementT
import Formalism.GaloisIrreducibility.NoSolvableTransitive
import Lemmata.GeneralBFactSecondBis.Imports

open Polynomial

noncomputable section

namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder

section PrimeTo

variable {M : Type*} [Monoid M]

/- English proof (translation)
Unfold `primeToPart`. Rewrite using `[h, ← pow_mul, ← pow_mul, mul_comm k]`.
-/
lemma primeToPart_pow (ℓ : ℕ) (x : M) (k : ℕ) (h : orderOf (x ^ k) = orderOf x) :
    primeToPart ℓ (x ^ k) = primeToPart ℓ x ^ k := by
  unfold primeToPart
  rw [h, ← pow_mul, ← pow_mul, mul_comm k]

/- English proof (translation)
Establish `hn0 : orderOf x ≠ 0` using `hx.orderOf_pos.ne'`. Establish `hm : orderOf x = ℓ ^ (orderOf x).factorization ℓ * (orderOf x / ℓ ^ (orderOf x).factorization ℓ)` using `(Nat.ordProj_mul_ordCompl_eq_self (orderOf x) ℓ).symm`. Establish `key : ∀ u : ℕ, (x ^ (ℓ ^ (orderOf x).factorization ℓ * u)) ^ (orderOf x / ℓ ^ (orderOf x).factorization ℓ) = 1` using `fun u => by`. Rewrite using `[← pow_mul, show ℓ ^ (orderOf x).factorization ℓ * u * (orderOf x / ℓ ^ (orderOf x).factorization ℓ) = (ℓ ^ (orderOf x).factorization ℓ * (orderOf x / ℓ ^ (orderOf x).factorization ℓ)) * u by ring, ← hm, pow_mul, pow_orderOf_eq_one, one_pow]`. Establish `hdvd : orderOf (primeToPart ℓ x) ∣ orderOf x / ℓ ^ (orderOf x).factorization ℓ` using `orderOf_dvd_of_pow_eq_one (key _)`.

Conclude with `Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_ordCompl hℓ hn0).symm`.
-/
lemma primeToPart_coprime {ℓ : ℕ} (hℓ : ℓ.Prime) (x : M) (hx : IsOfFinOrder x) :
    (orderOf (primeToPart ℓ x)).Coprime ℓ := by
  have hn0 : orderOf x ≠ 0 := hx.orderOf_pos.ne'
  have hm : orderOf x = ℓ ^ (orderOf x).factorization ℓ * (orderOf x / ℓ ^ (orderOf x).factorization ℓ) :=
    (Nat.ordProj_mul_ordCompl_eq_self (orderOf x) ℓ).symm
  have key : ∀ u : ℕ, (x ^ (ℓ ^ (orderOf x).factorization ℓ * u)) ^
      (orderOf x / ℓ ^ (orderOf x).factorization ℓ) = 1 := fun u => by
    rw [← pow_mul, show ℓ ^ (orderOf x).factorization ℓ * u * (orderOf x / ℓ ^ (orderOf x).factorization ℓ)
      = (ℓ ^ (orderOf x).factorization ℓ * (orderOf x / ℓ ^ (orderOf x).factorization ℓ)) * u by ring,
      ← hm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hdvd : orderOf (primeToPart ℓ x) ∣ orderOf x / ℓ ^ (orderOf x).factorization ℓ :=
    orderOf_dvd_of_pow_eq_one (key _)
  exact Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_ordCompl hℓ hn0).symm

/- English proof (translation)
The claim follows from `hx.pow`.
-/
lemma primeToPart_isOfFinOrder (ℓ : ℕ) (x : M) (hx : IsOfFinOrder x) :
    IsOfFinOrder (primeToPart ℓ x) := hx.pow

end PrimeTo

section Frob

variable {g : ℕ} [hg : Fact g.Prime]

/- English proof (translation)
The claim follows from `RingHom.ext_zmod _ _`.
-/
lemma frob_comp_alg : (frobenius (Fbar g) g).comp (algebraMap (ZMod g) (Fbar g)) =
    algebraMap (ZMod g) (Fbar g) := RingHom.ext_zmod _ _

/- English proof (translation)
Rewrite using `[eval_map, eval_map, ← frobenius_def, ← frobenius_def, hom_eval₂, frob_comp_alg]`.
-/
lemma eval_pow_map (p : (ZMod g)[X]) (x : Fbar g) :
    (p.map (algebraMap (ZMod g) (Fbar g))).eval (x ^ g) =
      ((p.map (algebraMap (ZMod g) (Fbar g))).eval x) ^ g := by
  rw [eval_map, eval_map, ← frobenius_def, ← frobenius_def, hom_eval₂, frob_comp_alg]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_second_bis.goal1 .. | (apply Bl.general_b_fact_second_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_sec …`.
-/
lemma mem_range_of_pow_eq (c : Fbar g) (hc : c ^ g = c) :
    c ∈ Set.range (algebraMap (ZMod g) (Fbar g)) := by
  first | exact Bl.general_b_fact_second_bis.goal1 .. | (apply Bl.general_b_fact_second_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_bis.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second_bis.goal1 <;> assumption) | (apply @Bl.general_b_fact_second_bis.goal1 <;> first | assumption | infer_instance)

end Frob

section Roots

variable {g : ℕ} [hg : Fact g.Prime]

structure GoodPoly (N : ℕ) (f : (ZMod g)[X]) : Prop where
  monic : f.Monic
  deg : f.natDegree = N
  coeff0 : f.coeff 0 ≠ 0
  sqf : Squarefree f

variable {N : ℕ} {f : (ZMod g)[X]}

/- English proof (translation)
The claim follows from `(hf.monic.map _).ne_zero`.
-/
lemma map_ne_zero' (hf : GoodPoly N f) : f.map (algebraMap (ZMod g) (Fbar g)) ≠ 0 :=
  (hf.monic.map _).ne_zero

/- English proof (translation)
Unfold `rootsBar`. Rewrite using `[mem_roots (map_ne_zero' hf)]`. Both sides reduce to the same expression.
-/
lemma mem_rootsBar (hf : GoodPoly N f) {x : Fbar g} :
    x ∈ rootsBar f ↔ (f.map (algebraMap (ZMod g) (Fbar g))).eval x = 0 := by
  unfold rootsBar; rw [mem_roots (map_ne_zero' hf)]; rfl

/- English proof (translation)
The claim follows from `nodup_roots ((PerfectField.separable_iff_squarefree.mpr hf.sqf).map)`.
-/
lemma rootsBar_nodup (hf : GoodPoly N f) : (rootsBar f).Nodup :=
  nodup_roots ((PerfectField.separable_iff_squarefree.mpr hf.sqf).map)

/- English proof (translation)
Unfold `rootsBar`. Rewrite using `[IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hf.deg]`.
-/
lemma rootsBar_card (hf : GoodPoly N f) : (rootsBar f).card = N := by
  unfold rootsBar; rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hf.deg]

/- English proof (translation)
Introduce and unpack `rfl`. Establish `h` using `(mem_rootsBar hf).mp hx`. Rewrite `h` using `[← coeff_zero_eq_eval_zero, coeff_map]`. Conclude with `hf.coeff0 ((map_eq_zero_iff _ (algebraMap (ZMod g) (Fbar g)).injective).mp h)`.
-/
lemma ne_zero_of_mem (hf : GoodPoly N f) {x : Fbar g} (hx : x ∈ rootsBar f) : x ≠ 0 := by
  rintro rfl
  have h := (mem_rootsBar hf).mp hx
  rw [← coeff_zero_eq_eval_zero, coeff_map] at h
  exact hf.coeff0 ((map_eq_zero_iff _ (algebraMap (ZMod g) (Fbar g)).injective).mp h)

/- English proof (translation)
Rewrite using `[mem_rootsBar hf, eval_pow_map, (mem_rootsBar hf).mp hx, zero_pow hg.out.ne_zero]`.
-/
lemma pow_mem (hf : GoodPoly N f) {x : Fbar g} (hx : x ∈ rootsBar f) : x ^ g ∈ rootsBar f := by
  rw [mem_rootsBar hf, eval_pow_map, (mem_rootsBar hf).mp hx, zero_pow hg.out.ne_zero]

/- English proof (translation)
Use `set Rt := (rootsBar f).toFinset`. Establish `hc : Fintype.card Rt = N`. Rewrite using `[Fintype.card_coe, Multiset.toFinset_card_of_nodup (rootsBar_nodup hf), rootsBar_card hf]`. Use `set e := (Fintype.equivFinOfCardEq hc).symm`. Use `set r : Fin N → Fbar g := fun i => (e i : Fbar g) with hrdef`.

Establish `hr : Function.Injective r` using `fun i j h => e.injective (Subtype.ext h)`. Establish `hmem : ∀ i, r i ∈ rootsBar f` using `fun i => Multiset.mem_toFinset.mp (e i).2`. Establish `hsurj : ∀ x ∈ rootsBar f, ∃ i, r i = x` using `fun x hx => ⟨e.symm ⟨x, Multiset.mem_toFinset.mpr hx⟩, by simp [r]⟩`. Use `choose s hs using fun i => hsurj _ (pow_mem hf (hmem i))`. Establish `hsinj : Function.Injective s` using `fun i j h => hr (frobenius_inj (Fbar g) g (by`.

Simplify using `only [frobenius_def]`. Rewrite using `[← hs i, ← hs j, h]))`. Use `⟨r, Equiv.ofBijective s (Finite.injective_iff_bijective.mp hsinj), hr, ?_, fun i => (hs i)⟩` and prove the remaining obligations. Use `(Multiset.Nodup.ext (Multiset.Nodup.map hr Finset.univ.nodup) (rootsBar_nodup hf)).mpr ?_` and prove the remaining obligations. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨i, -, rfl⟩` from `Multiset.mem_map.mp h`. Conclude with `hmem i`. Introduce `h`.

Take `⟨i, rfl⟩` from `hsurj x h`. Conclude with `Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)`.
-/
lemma exists_index (hf : GoodPoly N f) : ∃ (r : Fin N → Fbar g) (σ : Equiv.Perm (Fin N)),
    Function.Injective r ∧ Finset.univ.val.map r = rootsBar f ∧ (∀ i, r (σ i) = r i ^ g) := by
  classical
  set Rt := (rootsBar f).toFinset
  have hc : Fintype.card Rt = N := by
    rw [Fintype.card_coe, Multiset.toFinset_card_of_nodup (rootsBar_nodup hf), rootsBar_card hf]
  set e := (Fintype.equivFinOfCardEq hc).symm
  set r : Fin N → Fbar g := fun i => (e i : Fbar g) with hrdef
  have hr : Function.Injective r := fun i j h => e.injective (Subtype.ext h)
  have hmem : ∀ i, r i ∈ rootsBar f := fun i => Multiset.mem_toFinset.mp (e i).2
  have hsurj : ∀ x ∈ rootsBar f, ∃ i, r i = x := fun x hx =>
    ⟨e.symm ⟨x, Multiset.mem_toFinset.mpr hx⟩, by simp [r]⟩
  choose s hs using fun i => hsurj _ (pow_mem hf (hmem i))
  have hsinj : Function.Injective s := fun i j h => hr (frobenius_inj (Fbar g) g (by
    simp only [frobenius_def]; rw [← hs i, ← hs j, h]))
  refine ⟨r, Equiv.ofBijective s (Finite.injective_iff_bijective.mp hsinj), hr, ?_,
    fun i => (hs i)⟩
  refine (Multiset.Nodup.ext (Multiset.Nodup.map hr Finset.univ.nodup) (rootsBar_nodup hf)).mpr ?_
  intro x; constructor
  · intro h; obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp h; exact hmem i
  · intro h; obtain ⟨i, rfl⟩ := hsurj x h; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)

variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hσ, ih, ← pow_mul, pow_succ]`.
-/
lemma iter_eq (hσ : ∀ i, r (σ i) = r i ^ g) (n : ℕ) (i : Fin N) :
    r ((σ ^ n) i) = r i ^ (g ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, hσ, ih, ← pow_mul, pow_succ]

/- English proof (translation)
Establish `hM` using `orderOf_pos σ`. Establish `h1` using `iter_eq hσ (orderOf σ) i`. Rewrite `h1` using `[pow_orderOf_eq_one, Equiv.Perm.one_apply]`. Establish `h2 : 2 ≤ g ^ orderOf σ`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[isOfFinOrder_iff_pow_eq_one]`. Use `⟨g ^ orderOf σ - 1, by omega, ?_⟩` and prove the remaining obligations. Apply `mul_right_cancel₀ h0` to reduce the goal to its premises. Rewrite using `[← pow_succ, Nat.sub_add_cancel (by omega), one_mul, ← h1]`.
-/
lemma isOfFinOrder_of_index (hσ : ∀ i, r (σ i) = r i ^ g) (i : Fin N) (h0 : r i ≠ 0) :
    IsOfFinOrder (r i) := by
  have hM := orderOf_pos σ
  have h1 := iter_eq hσ (orderOf σ) i
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at h1
  have h2 : 2 ≤ g ^ orderOf σ := by
    calc 2 ≤ g := hg.out.two_le
      _ = g ^ 1 := (pow_one g).symm
      _ ≤ g ^ orderOf σ := Nat.pow_le_pow_right hg.out.pos hM
  rw [isOfFinOrder_iff_pow_eq_one]
  refine ⟨g ^ orderOf σ - 1, by omega, ?_⟩
  apply mul_right_cancel₀ h0
  rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, ← h1]

/- English proof (translation)
Use `set P : (Fbar g)[X] := ((S.val.map r).map fun a => X - C a).prod with hPdef`. Establish `hPm : P.Monic` using `monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)`. Establish `hSσ : S.map σ.toEmbedding = S` using `Finset.eq_of_subset_of_card_le (fun y hy => by`. Take `⟨x, hx, rfl⟩` from `Finset.mem_map.mp hy; exact hS x hx) (by rw [Finset.card_map])`. Establish `hfrob : P.map (frobenius (Fbar g) g) = P`.

Rewrite using `[hPdef, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]`. Use `conv_rhs => rw [← hSσ]`. Rewrite using `[Finset.map_val, Multiset.map_map, Multiset.map_map]`. Use `congr 1`. Apply `Multiset.map_congr rfl` to reduce the goal to its premises.

Introduce `i _`. Simplify using `[frobenius_def, hσ]`. Establish `hlift : P ∈ lifts (algebraMap (ZMod g) (Fbar g))`. Rewrite using `[lifts_iff_coeff_lifts]`. Introduce `n`.

Apply `mem_range_of_pow_eq` to reduce the goal to its premises. Use `congrArg (fun p => p.coeff n) hfrob` as an intermediate fact. Simplify `this` using `[coeff_map, frobenius_def]`. Take `⟨Q, hQP, hQd, hQm⟩` from `lifts_and_natDegree_eq_and_monic hlift hPm`. Establish `hPdvd : P ∣ f.map (algebraMap (ZMod g) (Fbar g))`.

Rewrite using `[hPdef, Multiset.prod_X_sub_C_dvd_iff_le_roots (map_ne_zero' hf)]`. Express the relevant statement in the definitionally equal form `S.val.map r ≤ rootsBar f`. Rewrite using `[← hrf]`. Conclude with `Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ S))`. Use `⟨Q, hQm, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_dvd_map (algebraMap (ZMod g) (Fbar g)) (algebraMap (ZMod g) (Fbar g)).injective hQm, hQP]`. Conclude with `hPdvd`. Rewrite using `[hQd, hPdef, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, Finset.card_val]`. Introduce `i hi`. Rewrite using `[hQP]`.

Establish `: r i ∈ P.roots`. Rewrite using `[hPdef, roots_multiset_prod_X_sub_C]`. Conclude with `Multiset.mem_map_of_mem _ hi`. Conclude with `(mem_roots hPm.ne_zero).mp this`.
-/
lemma exists_dvd (hf : GoodPoly N f) (hrf : Finset.univ.val.map r = rootsBar f)
    (hσ : ∀ i, r (σ i) = r i ^ g) (S : Finset (Fin N)) (hS : ∀ i ∈ S, σ i ∈ S) :
    ∃ Q : (ZMod g)[X], Q.Monic ∧ Q ∣ f ∧ Q.natDegree = S.card ∧
      ∀ i ∈ S, (Q.map (algebraMap (ZMod g) (Fbar g))).eval (r i) = 0 := by
  classical
  set P : (Fbar g)[X] := ((S.val.map r).map fun a => X - C a).prod with hPdef
  have hPm : P.Monic := monic_multiset_prod_of_monic _ _ (fun a _ => monic_X_sub_C a)
  have hSσ : S.map σ.toEmbedding = S :=
    Finset.eq_of_subset_of_card_le (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy; exact hS x hx) (by rw [Finset.card_map])
  have hfrob : P.map (frobenius (Fbar g) g) = P := by
    rw [hPdef, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
    conv_rhs => rw [← hSσ]
    rw [Finset.map_val, Multiset.map_map, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro i _
    simp [frobenius_def, hσ]
  have hlift : P ∈ lifts (algebraMap (ZMod g) (Fbar g)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    apply mem_range_of_pow_eq
    have := congrArg (fun p => p.coeff n) hfrob
    simpa [coeff_map, frobenius_def] using this
  obtain ⟨Q, hQP, hQd, hQm⟩ := lifts_and_natDegree_eq_and_monic hlift hPm
  have hPdvd : P ∣ f.map (algebraMap (ZMod g) (Fbar g)) := by
    rw [hPdef, Multiset.prod_X_sub_C_dvd_iff_le_roots (map_ne_zero' hf)]
    change S.val.map r ≤ rootsBar f
    rw [← hrf]
    exact Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ S))
  refine ⟨Q, hQm, ?_, ?_, ?_⟩
  · rw [← map_dvd_map (algebraMap (ZMod g) (Fbar g)) (algebraMap (ZMod g) (Fbar g)).injective hQm, hQP]
    exact hPdvd
  · rw [hQd, hPdef, natDegree_multiset_prod_X_sub_C_eq_card, Multiset.card_map, Finset.card_val]
  · intro i hi
    rw [hQP]
    have : r i ∈ P.roots := by
      rw [hPdef, roots_multiset_prod_X_sub_C]; exact Multiset.mem_map_of_mem _ hi
    exact (mem_roots hPm.ne_zero).mp this

end Roots

section Cycle

variable {g : ℕ} [hg : Fact g.Prime] {N : ℕ} {f : (ZMod g)[X]}
variable {r : Fin N → Fbar g} {σ : Equiv.Perm (Fin N)}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using hx`. Consider the case `succ n ih => rw [pow_succ, pow_mul, eval_pow_map, ih, zero_pow hg.out.ne_zero]`.
-/
lemma eval_pow_iter (p : (ZMod g)[X]) (x : Fbar g)
    (hx : (p.map (algebraMap (ZMod g) (Fbar g))).eval x = 0) (n : ℕ) :
    (p.map (algebraMap (ZMod g) (Fbar g))).eval (x ^ (g ^ n)) = 0 := by
  induction n with
  | zero => simpa using hx
  | succ n ih => rw [pow_succ, pow_mul, eval_pow_map, ih, zero_pow hg.out.ne_zero]

/- English proof (translation)
Use `set alg := algebraMap (ZMod g) (Fbar g)`. Establish `hqdeg : (q.map alg).degree ≠ 0`. Rewrite using `[degree_map]`. Introduce `h`. Use `natDegree_eq_of_degree_eq_some h` as an intermediate fact.

Conclude with `hp.ne_zero this`. Take `⟨α, hα⟩` from `IsAlgClosed.exists_root (q.map alg) hqdeg`. Establish `hαf : α ∈ rootsBar f`. Rewrite using `[mem_rootsBar hf]`. Take `⟨c, hc⟩` from `hqf`.

Rewrite using `[hc, Polynomial.map_mul, eval_mul, hα.eq_zero, zero_mul]`. Take `⟨i0, -, hi0⟩` from `Multiset.mem_map.mp (hrf ▸ hαf : α ∈ Finset.univ.val.map r)`. Use `set O := Finset.univ.filter (fun j => σ.SameCycle i0 j) with hO`. Establish `hOs : ∀ j ∈ O, σ j ∈ O`. Introduce `j hj`.

Simplify using `only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢`. Conclude with `Equiv.Perm.sameCycle_apply_right.mpr hj`. Establish `hi0O : i0 ∈ O`. Rewrite using `[hO, Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩`.

Take `⟨Q, hQm, hQf, hQd, hQr⟩` from `exists_dvd hf hrf hσ O hOs`. Establish `hqQ : q ∣ Q`. Assume the negation of the conclusion as `hnd`. Take `⟨a, b, hab⟩` from `(Irreducible.coprime_iff_not_dvd hq).mpr hnd`. Use `congrArg (fun p => (p.map alg).eval α) hab` as an intermediate fact.

Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, eval_add, eval_mul, eval_one] at this`. Rewrite `this` using `[hα.eq_zero, ← hi0, hQr i0 hi0O]`. Simplify using `at this`. Establish `hle1 : q.natDegree ≤ O.card` using `hQd ▸ natDegree_le_of_dvd hqQ hQm.ne_zero`. Establish `hle2 : O.card ≤ q.natDegree`.

Establish `hq0 : q.map alg ≠ 0` using `(Polynomial.map_ne_zero_iff alg.injective).mpr hq.ne_zero`. Establish `hsub : O.image r ⊆ (q.map alg).roots.toFinset`. Introduce `y hy`. Take `⟨j, hj, rfl⟩` from `Finset.mem_image.mp hy`. Simplify using `only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at hj`.

Take `⟨n, hn⟩` from `hj.exists_nat_pow_eq`. Rewrite using `[Multiset.mem_toFinset, mem_roots hq0, IsRoot, ← hn, iter_eq hσ, hi0]`. Conclude with `eval_pow_iter q α hα.eq_zero n`. Combine the equalities or inequalities in the displayed calculation. Establish `hcard : O.card = q.natDegree` using `le_antisymm hle2 hle1`.

Establish `hmove : σ i0 ≠ i0`. Introduce `hfix`. Establish `: O = {i0}`. Use extensionality with `j`. Simplify using `only [hO, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(h.eq_of_left hfix).symm`. Introduce and unpack `rfl`. Conclude with `Equiv.Perm.SameCycle.refl _ _`.

Rewrite `hcard` using `[this, Finset.card_singleton]`. Conclude with `hp.one_lt.ne hcard`. Establish `hsupp : (σ.cycleOf i0).support = O`. Use extensionality with `j`. Rewrite using `[Equiv.Perm.mem_support_cycleOf_iff]`.

Simplify using `[hO, Equiv.Perm.mem_support, hmove]`. Rewrite using `[Equiv.Perm.cycleType_def, Multiset.mem_map]`. Use `⟨σ.cycleOf i0, ?_, ?_⟩` and prove the remaining obligations. Conclude with `Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hmove)`. Simplify using `[hsupp, hcard]`.
-/
lemma mem_cycleType_of_factor (hf : GoodPoly N f) (hr : Function.Injective r)
    (hrf : Finset.univ.val.map r = rootsBar f) (hσ : ∀ i, r (σ i) = r i ^ g)
    (q : (ZMod g)[X]) (hq : Irreducible q) (hqf : q ∣ f) (hp : q.natDegree.Prime) :
    q.natDegree ∈ σ.cycleType := by
  classical
  set alg := algebraMap (ZMod g) (Fbar g)
  have hqdeg : (q.map alg).degree ≠ 0 := by
    rw [degree_map]; intro h
    have := natDegree_eq_of_degree_eq_some h
    exact hp.ne_zero this
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root (q.map alg) hqdeg
  have hαf : α ∈ rootsBar f := by
    rw [mem_rootsBar hf]
    obtain ⟨c, hc⟩ := hqf
    rw [hc, Polynomial.map_mul, eval_mul, hα.eq_zero, zero_mul]
  obtain ⟨i0, -, hi0⟩ := Multiset.mem_map.mp (hrf ▸ hαf : α ∈ Finset.univ.val.map r)
  set O := Finset.univ.filter (fun j => σ.SameCycle i0 j) with hO
  have hOs : ∀ j ∈ O, σ j ∈ O := by
    intro j hj
    simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact Equiv.Perm.sameCycle_apply_right.mpr hj
  have hi0O : i0 ∈ O := by
    rw [hO, Finset.mem_filter]; exact ⟨Finset.mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩
  obtain ⟨Q, hQm, hQf, hQd, hQr⟩ := exists_dvd hf hrf hσ O hOs

  have hqQ : q ∣ Q := by
    by_contra hnd
    obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hq).mpr hnd
    have := congrArg (fun p => (p.map alg).eval α) hab
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, eval_add, eval_mul,
      eval_one] at this
    rw [hα.eq_zero, ← hi0, hQr i0 hi0O] at this
    simp at this
  have hle1 : q.natDegree ≤ O.card := hQd ▸ natDegree_le_of_dvd hqQ hQm.ne_zero
  have hle2 : O.card ≤ q.natDegree := by
    have hq0 : q.map alg ≠ 0 := (Polynomial.map_ne_zero_iff alg.injective).mpr hq.ne_zero
    have hsub : O.image r ⊆ (q.map alg).roots.toFinset := by
      intro y hy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      obtain ⟨n, hn⟩ := hj.exists_nat_pow_eq
      rw [Multiset.mem_toFinset, mem_roots hq0, IsRoot, ← hn, iter_eq hσ, hi0]
      exact eval_pow_iter q α hα.eq_zero n
    calc O.card = (O.image r).card := (Finset.card_image_of_injective O hr).symm
      _ ≤ (q.map alg).roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ (q.map alg).roots.card := Multiset.toFinset_card_le _
      _ ≤ (q.map alg).natDegree := card_roots' _
      _ = q.natDegree := natDegree_map _
  have hcard : O.card = q.natDegree := le_antisymm hle2 hle1
  have hmove : σ i0 ≠ i0 := by
    intro hfix
    have : O = {i0} := by
      ext j
      simp only [hO, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h; exact (h.eq_of_left hfix).symm
      · rintro rfl; exact Equiv.Perm.SameCycle.refl _ _
    rw [this, Finset.card_singleton] at hcard
    exact hp.one_lt.ne hcard
  have hsupp : (σ.cycleOf i0).support = O := by
    ext j
    rw [Equiv.Perm.mem_support_cycleOf_iff]
    simp [hO, Equiv.Perm.mem_support, hmove]
  rw [Equiv.Perm.cycleType_def, Multiset.mem_map]
  refine ⟨σ.cycleOf i0, ?_, ?_⟩
  · exact Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hmove)
  · simp [hsupp, hcard]

end Cycle

section Orbits

variable {α K : Type*} [Fintype α] [DecidableEq α] [DecidableEq K] [Monoid K]
variable (σ : Equiv.Perm α) (L : α → K)

def cyc (i : α) : Finset α := Finset.univ.filter (fun j => σ.SameCycle i j)

def blocks : Finset (Finset K) := Finset.univ.image (fun i => (cyc σ i).image L)

variable {σ L}

/- English proof (translation)
Simplify using `[cyc]`.
-/
lemma mem_cyc {i j : α} : j ∈ cyc σ i ↔ σ.SameCycle i j := by simp [cyc]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', Equiv.Perm.mul_apply, hL]`.
-/
lemma iterate_eq {q : ℕ} (hL : ∀ i, L (σ i) = L i ^ q) (n : ℕ) (j : α) :
    (fun x : K => x ^ q)^[n] (L j) = L ((σ ^ n) j) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', Equiv.Perm.mul_apply, hL]

/- English proof (translation)
Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp hS`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Take `⟨j, hj, rfl⟩` from `Finset.mem_image.mp hx`. Use `show L j ^ q ∈ _`.

Rewrite using `[← hL]`. Conclude with `Finset.mem_image_of_mem _ (mem_cyc.mpr (Equiv.Perm.sameCycle_apply_right.mpr (mem_cyc.mp hj)))`. Introduce `x hx y hy`. Take `⟨j, hj, rfl⟩` from `Finset.mem_image.mp hx`. Take `⟨k, hk, rfl⟩` from `Finset.mem_image.mp hy`.

Take `⟨n, hn⟩` from `((mem_cyc.mp hj).symm.trans (mem_cyc.mp hk)).exists_nat_pow_eq`. Conclude with `⟨n, by rw [iterate_eq hL, hn]⟩`.
-/
lemma isOrbit_of_mem {q : ℕ} (hL : ∀ i, L (σ i) = L i ^ q) {S : Finset K} (hS : S ∈ blocks σ L) :
    Formalism.GaloisIrreducibility.IsOrbit (fun x : K => x ^ q) S := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
  constructor
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    show L j ^ q ∈ _
    rw [← hL]
    exact Finset.mem_image_of_mem _ (mem_cyc.mpr (Equiv.Perm.sameCycle_apply_right.mpr (mem_cyc.mp hj)))
  · intro x hx y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨n, hn⟩ := ((mem_cyc.mp hj).symm.trans (mem_cyc.mp hk)).exists_nat_pow_eq
    exact ⟨n, by rw [iterate_eq hL, hn]⟩

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [mem_cyc] at *`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `hk.trans (hj.symm.trans h)`.

Introduce `h`. Conclude with `hj.trans (hk.symm.trans h)`.
-/
lemma cyc_eq_of_mem {i j k : α} (hj : k ∈ cyc σ i) (hk : k ∈ cyc σ j) : cyc σ i = cyc σ j := by
  ext x
  simp only [mem_cyc] at *
  constructor
  · intro h; exact hk.trans (hj.symm.trans h)
  · intro h; exact hj.trans (hk.symm.trans h)

/- English proof (translation)
Take `⟨i, -, rfl⟩` from `Finset.mem_image.mp hS`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.mp hT`. Rewrite using `[Finset.disjoint_left]`. Introduce `x hx hx'`. Take `⟨a, ha, rfl⟩` from `Finset.mem_image.mp hx`.

Take `⟨b, hb, hba⟩` from `Finset.mem_image.mp hx'`. Rewrite `hb` using `[hLi hba]`. Conclude with `hST (by rw [cyc_eq_of_mem ha hb])`.
-/
lemma blocks_disjoint (hLi : Function.Injective L) {S T : Finset K} (hS : S ∈ blocks σ L)
    (hT : T ∈ blocks σ L) (hST : S ≠ T) : Disjoint S T := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hT
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hx'
  rw [hLi hba] at hb
  exact hST (by rw [cyc_eq_of_mem ha hb])

/- English proof (translation)
Proceed by induction on `I using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert S I hSI ih`. Rewrite using `[Finset.sum_insert hSI, ih (fun A hA B hB h => hI A (Finset.mem_insert_of_mem hA) B (Finset.mem_insert_of_mem hB) h), Finset.biUnion_insert]`. Establish `hd : Disjoint S (I.biUnion id)`.

Rewrite using `[Finset.disjoint_biUnion_right]`. Introduce `T hT`. Conclude with `hI S (Finset.mem_insert_self _ _) T (Finset.mem_insert_of_mem hT) (fun h => hSI (h ▸ hT))`. Express the relevant statement in the definitionally equal form `S.val + _ = (S ∪ _).val`. Rewrite using `[← Finset.disjUnion_eq_union _ _ hd]`.

Both sides reduce to the same expression.
-/
lemma sum_val_eq_biUnion (I : Finset (Finset K))
    (hI : ∀ S ∈ I, ∀ T ∈ I, S ≠ T → Disjoint S T) :
    ∑ S ∈ I, S.val = (I.biUnion id).val := by
  induction I using Finset.induction_on with
  | empty => simp
  | insert S I hSI ih =>
    rw [Finset.sum_insert hSI, ih (fun A hA B hB h => hI A (Finset.mem_insert_of_mem hA) B
      (Finset.mem_insert_of_mem hB) h), Finset.biUnion_insert]
    have hd : Disjoint S (I.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro T hT
      exact hI S (Finset.mem_insert_self _ _) T (Finset.mem_insert_of_mem hT)
        (fun h => hSI (h ▸ hT))
    change S.val + _ = (S ∪ _).val
    rw [← Finset.disjUnion_eq_union _ _ hd]
    rfl

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Finset.mem_biUnion, id, Finset.mem_image, Finset.mem_univ, true_and, blocks]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨S, ⟨i, rfl⟩, hx⟩`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.mp hx`.

Conclude with `⟨j, rfl⟩`. Introduce and unpack `⟨j, rfl⟩`. Conclude with `⟨_, ⟨j, rfl⟩, Finset.mem_image_of_mem _ (mem_cyc.mpr (Equiv.Perm.SameCycle.refl _ _))⟩`.
-/
lemma biUnion_blocks : (blocks σ L).biUnion id = Finset.univ.image L := by
  ext x
  simp only [Finset.mem_biUnion, id, Finset.mem_image, Finset.mem_univ, true_and, blocks]
  constructor
  · rintro ⟨S, ⟨i, rfl⟩, hx⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨j, rfl⟩, Finset.mem_image_of_mem _ (mem_cyc.mpr (Equiv.Perm.SameCycle.refl _ _))⟩

/- English proof (translation)
Rewrite using `[sum_val_eq_biUnion _ (fun S hS T hT h => blocks_disjoint hLi hS hT h), biUnion_blocks, Finset.image_val_of_injOn (fun a _ b _ h => hLi h)]`.
-/
lemma sum_blocks (hLi : Function.Injective L) :
    ∑ S ∈ blocks σ L, S.val = Finset.univ.val.map L := by
  rw [sum_val_eq_biUnion _ (fun S hS T hT h => blocks_disjoint hLi hS hT h), biUnion_blocks,
    Finset.image_val_of_injOn (fun a _ b _ h => hLi h)]

/- English proof (translation)
Proceed by induction on `m using Multiset.induction_on generalizing s with`. Consider the case `empty`. Simplify using `only [Multiset.map_zero, Multiset.le_zero] at h`. Conclude with `⟨0, le_rfl, by simp [h]⟩`. Consider the case `cons b m ih`.

Rewrite `h` using `[Multiset.map_cons]`. Distinguish the cases in `hb : f b ∈ s`. Establish `hs` using `Multiset.cons_erase hb`. Rewrite `h` using `[← hs, Multiset.cons_le_cons_iff]`. Take `⟨t, ht, htm⟩` from `ih _ h`.

Conclude with `⟨b ::ₘ t, Multiset.cons_le_cons _ ht, by rw [Multiset.map_cons, htm, hs]⟩`. Rewrite `h` using `[Multiset.le_cons_of_notMem hb]`. Take `⟨t, ht, htm⟩` from `ih _ h`. Conclude with `⟨t, ht.trans (Multiset.le_cons_self _ _), htm⟩`.
-/
lemma exists_le_map {β γ : Type*} (m : Multiset β) (f : β → γ) (s : Multiset γ)
    (h : s ≤ m.map f) : ∃ t ≤ m, t.map f = s := by
  classical
  induction m using Multiset.induction_on generalizing s with
  | empty =>
    simp only [Multiset.map_zero, Multiset.le_zero] at h
    exact ⟨0, le_rfl, by simp [h]⟩
  | cons b m ih =>
    rw [Multiset.map_cons] at h
    by_cases hb : f b ∈ s
    · have hs := Multiset.cons_erase hb
      rw [← hs, Multiset.cons_le_cons_iff] at h
      obtain ⟨t, ht, htm⟩ := ih _ h
      exact ⟨b ::ₘ t, Multiset.cons_le_cons _ ht, by rw [Multiset.map_cons, htm, hs]⟩
    · rw [Multiset.le_cons_of_notMem hb] at h
      obtain ⟨t, ht, htm⟩ := ih _ h
      exact ⟨t, ht.trans (Multiset.le_cons_self _ _), htm⟩

/- English proof (translation)
Take `⟨s, hs, hsum⟩` from `h`. Take `⟨t, ht, rfl⟩` from `exists_le_map _ _ _ hs`. Use `set T : Finset (Finset K) := ⟨t, Multiset.nodup_of_le ht (blocks σ L).nodup⟩`. Establish `hTsub : ∀ S ∈ T, S ∈ blocks σ L` using `fun S hS => Multiset.mem_of_le ht hS`. Use `⟨Finset.univ.filter (fun i => ∃ S ∈ T, L i ∈ S), ?_, ?_⟩` and prove the remaining obligations.

Introduce `i hi`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢`. Take `⟨S, hST, hiS⟩` from `hi`. Use `⟨S, hST, ?_⟩` and prove the remaining obligations. Take `⟨j, -, rfl⟩` from `Finset.mem_image.mp (hTsub S hST)`.

Take `⟨k, hk, hki⟩` from `Finset.mem_image.mp hiS`. Rewrite `hk` using `[hLi hki]`. Conclude with `Finset.mem_image_of_mem _ (mem_cyc.mpr (Equiv.Perm.sameCycle_apply_right.mpr (mem_cyc.mp hk)))`. Rewrite using `[← Finset.card_image_of_injective _ hLi]`. Establish `himg : (Finset.univ.filter (fun i => ∃ S ∈ T, L i ∈ S)).image L = T.biUnion id`.

Use extensionality with `x`. Simplify using `only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, id]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, ⟨S, hS, hiS⟩, rfl⟩`. Conclude with `⟨S, hS, hiS⟩`.

Introduce and unpack `⟨S, hS, hx⟩`. Take `⟨j, -, rfl⟩` from `Finset.mem_image.mp (hTsub S hS)`. Take `⟨k, -, rfl⟩` from `Finset.mem_image.mp hx`. Conclude with `⟨k, ⟨_, hS, hx⟩, rfl⟩`. Rewrite using `[himg, show T.biUnion id = T.biUnion (fun S => S) from rfl, Finset.card_biUnion (fun S hS T' hT' h => blocks_disjoint hLi (hTsub S hS) (hTsub T' hT') h), ← hsum]`.

Both sides reduce to the same expression.
-/
lemma stable_of_subSum (hLi : Function.Injective L) {a : ℕ}
    (h : Formalism.GaloisIrreducibility.IsSubSum ((blocks σ L).val.map Finset.card) a) :
    ∃ A : Finset α, (∀ i ∈ A, σ i ∈ A) ∧ A.card = a := by
  obtain ⟨s, hs, hsum⟩ := h
  obtain ⟨t, ht, rfl⟩ := exists_le_map _ _ _ hs
  set T : Finset (Finset K) := ⟨t, Multiset.nodup_of_le ht (blocks σ L).nodup⟩
  have hTsub : ∀ S ∈ T, S ∈ blocks σ L := fun S hS => Multiset.mem_of_le ht hS
  refine ⟨Finset.univ.filter (fun i => ∃ S ∈ T, L i ∈ S), ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    obtain ⟨S, hST, hiS⟩ := hi
    refine ⟨S, hST, ?_⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hTsub S hST)
    obtain ⟨k, hk, hki⟩ := Finset.mem_image.mp hiS
    rw [hLi hki] at hk
    exact Finset.mem_image_of_mem _ (mem_cyc.mpr (Equiv.Perm.sameCycle_apply_right.mpr (mem_cyc.mp hk)))
  · rw [← Finset.card_image_of_injective _ hLi]
    have himg : (Finset.univ.filter (fun i => ∃ S ∈ T, L i ∈ S)).image L = T.biUnion id := by
      ext x
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion, id]
      constructor
      · rintro ⟨i, ⟨S, hS, hiS⟩, rfl⟩; exact ⟨S, hS, hiS⟩
      · rintro ⟨S, hS, hx⟩
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (hTsub S hS)
        obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨k, ⟨_, hS, hx⟩, rfl⟩
    rw [himg, show T.biUnion id = T.biUnion (fun S => S) from rfl, Finset.card_biUnion (fun S hS T' hT' h =>
      blocks_disjoint hLi (hTsub S hS) (hTsub T' hT') h), ← hsum]
    rfl

end Orbits

section Lin

variable {K : Type*} [Field K] {N : ℕ}

def repGL : GL (Fin N) K →* Module.End K (Fin N → K) :=
  (MonoidHomClass.toMonoidHom (Matrix.toLinAlgEquiv' :
    Matrix (Fin N) (Fin N) K ≃ₐ[K] Module.End K (Fin N → K))).comp (Units.coeHom _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma repGL_eq (A : GL (Fin N) K) : repGL A = Matrix.toLin' (A : Matrix (Fin N) (Fin N) K) := rfl

/- English proof (translation)
Rewrite using `[repGL_eq, Matrix.toLin'_apply]`.
-/
lemma repGL_apply (A : GL (Fin N) K) (x : Fin N → K) :
    repGL A x = Matrix.mulVec (A : Matrix (Fin N) (Fin N) K) x := by
  rw [repGL_eq, Matrix.toLin'_apply]

/- English proof (translation)
Introduce `A B h`. Apply `Units.ext` to reduce the goal to its premises. Rewrite `h` using `[repGL_eq, repGL_eq]`. Conclude with `Matrix.toLin'.injective h`.
-/
lemma repGL_injective : Function.Injective (repGL (K := K) (N := N)) := by
  intro A B h
  apply Units.ext
  rw [repGL_eq, repGL_eq] at h
  exact Matrix.toLin'.injective h

/- English proof (translation)
Rewrite using `[repGL_eq, Matrix.charpoly_toLin']`.
-/
lemma charpoly_repGL (A : GL (Fin N) K) :
    LinearMap.charpoly (repGL A) = (A : Matrix (Fin N) (Fin N) K).charpoly := by
  rw [repGL_eq, Matrix.charpoly_toLin']

def glEquiv (A : GL (Fin N) K) : (Fin N → K) ≃ₗ[K] (Fin N → K) :=
  LinearEquiv.ofLinearMap (repGL A) (repGL A⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one, Module.End.one_eq_id])
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one, Module.End.one_eq_id])

/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma glEquiv_apply (A : GL (Fin N) K) (x : Fin N → K) : glEquiv A x = repGL A x := rfl

end Lin

/- English proof (translation)
Introduce `N g hgf PP J f χ _hBB hgood ℓ hℓf i hℓ G hGg ρ τ φ ι hconj hinj hchar`. Establish `hℓp : ℓ.Prime` using `hℓf.out`. Establish `hℓg : ℓ ≠ g i` using `fun h => hℓ (by rw [h]; exact Set.mem_union_left _ (Set.mem_singleton _))`. Take `⟨hG1, hG2, hG3, hG4, hG5, hG6⟩` from `hgood i`. Establish `hpoly : ∀ v, GoodPoly N (f i v)` using `fun v => ⟨(hG1 v).1, (hG1 v).2.1, (hG1 v).2.2, hG2 v⟩`.

Use `choose r σ hr hrf hσ using fun v => exists_index (hpoly v)`. Establish `hmemr : ∀ v j, r v j ∈ rootsBar (f i v)`. Introduce `v j`. Rewrite using `[← hrf v]`. Conclude with `Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)`.

Establish `hr0 : ∀ v j, r v j ≠ 0` using `fun v j => ne_zero_of_mem (hpoly v) (hmemr v j)`. Establish `hrfin : ∀ v j, IsOfFinOrder (r v j)` using `fun v j => isOfFinOrder_of_index (hσ v) j (hr0 v j)`. Use `set L : PP i → Fin N → Fbar ℓ := fun v j => ι v (primeToPart ℓ (r v j)) with hLdef`. Establish `hptp0 : ∀ v j, primeToPart ℓ (r v j) ≠ 0`. Introduce `v j`.

Unfold `primeToPart`. Conclude with `pow_ne_zero _ (hr0 v j)`. Establish `hptpc : ∀ v j, (orderOf (primeToPart ℓ (r v j))).Coprime ℓ` using `fun v j => primeToPart_coprime hℓp _ (hrfin v j)`. Establish `hLinj : ∀ v, Function.Injective (L v)`. Introduce `v j k h`.

Establish `h1` using `hinj v _ _ (hptp0 v j) (hptp0 v k) (hptpc v j) (hptpc v k) h`. Conclude with `hr v (hG3 ℓ hℓp hℓ v _ (hmemr v j) _ (hmemr v k) h1)`. Establish `hLσ : ∀ v j, L v (σ v j) = L v j ^ (g i)`. Introduce `v j`. Use `show ι v (primeToPart ℓ (r v (σ v j))) = ι v (primeToPart ℓ (r v j)) ^ (g i)`.

Rewrite using `[hσ v j, primeToPart_pow, map_pow]`. Conclude with `orderOf_injective (frobenius (Fbar (g i)) (g i)).toMonoidHom (frobenius_inj _ _) (r v j)`. Establish `hroots : ∀ v, (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly.roots = Finset.univ.val.map (L v)`. Introduce `v`. Establish `hcp : (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly = ((Finset.univ.val.map (L v)).map fun a => X - C a).prod`.

Rewrite using `[hchar v, ← hrf v, Multiset.map_map, Multiset.map_map]`. Both sides reduce to the same expression. Rewrite using `[hcp, roots_multiset_prod_X_sub_C]`. Establish `hirr : IrredOn ρ ⊤`. Introduce `W hW`.

Use `Formalism.GaloisIrreducibility.irred (Fbar ℓ) (Fin N → Fbar ℓ) (PP i) (Finset (Fbar ℓ)) (fun v => repGL (ρ (τ v))) (fun v => glEquiv (ρ (φ v))) (fun _ => g i) (fun _ S => S) (fun v => blocks (σ v) (L v)) ?_ ?_ ?_ ?_ W ?_ ?_` and prove the remaining obligations. Introduce `v x show repGL (ρ (φ v)) (repGL (ρ (τ v)) x) = (repGL (ρ (τ v)) ^ g i) (repGL (ρ (φ v)) x)`. Establish `heq : ρ (φ v) * ρ (τ v) = ρ (τ v) ^ g i * ρ (φ v)`. Establish `h` using `hconj v`. Rewrite `h` using `[map_mul, map_mul, map_inv]`.

Rewrite using `[← h, inv_mul_cancel_right]`. Rewrite using `[← map_pow, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul repGL, ← map_mul repGL, heq]`. Introduce `v S hS`. Conclude with `isOrbit_of_mem (hLσ v) hS`. Introduce `v show (LinearMap.charpoly (repGL (ρ (τ v)))).roots = _`.

Rewrite using `[charpoly_repGL, hroots v, sum_blocks (hLinj v)]`. Introduce `a ha h2a`. Rewrite `h2a` using `[Module.finrank_fintype_fun_eq_card, Fintype.card_fin]`. Take `⟨v, hv⟩` from `hG5 a ha h2a`. Use `⟨v, fun hs => hv ?_⟩` and prove the remaining obligations.

Take `⟨A, hA, hAc⟩` from `stable_of_subSum (hLinj v) hs`. Take `⟨Q, -, hQf, hQd, -⟩` from `exists_dvd (hpoly v) (hrf v) (hσ v) A hA`. Conclude with `⟨Q, hQf, hQd.trans hAc⟩`. Introduce `v x hx show repGL (ρ (τ v)) x ∈ W`. Rewrite using `[repGL_apply]`.

Conclude with `hW _ (Subgroup.mem_top _) x hx`. Introduce `v x hx show glEquiv (ρ (φ v)) x ∈ W`. Rewrite using `[glEquiv_apply, repGL_apply]`. Conclude with `hW _ (Subgroup.mem_top _) x hx`. Establish `hpart3 : ∀ v j, ¬ (Matrix.charpoly (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ))).IsRoot (ι v (primeToPart ℓ (algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i)))))`.

Introduce `v j hroot`. Establish `hmem` using `(mem_roots (Matrix.charpoly_monic _).ne_zero).mpr hroot`. Rewrite `hmem` using `[hroots v]`. Take `⟨k, -, hk⟩` from `Multiset.mem_map.mp hmem`. Establish `hc0 : algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i)) ≠ 0` using `(_root_.map_ne_zero _).mpr (χ i v j).ne_zero`.

Establish `hcfin : IsOfFinOrder (algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i)))` using `MonoidHom.isOfFinOrder ((algebraMap (ZMod (g i)) (Fbar (g i))).toMonoidHom.comp (Units.coeHom _)) (isOfFinOrder_of_finite (χ i v j))`. Establish `h1` using `hinj v _ _ (hptp0 v k) (by unfold primeToPart; exact pow_ne_zero _ hc0) (hptpc v k) (primeToPart_coprime hℓp _ hcfin) hk`. Conclude with `hG4 ℓ hℓp hℓg v j _ (hmemr v k) h1`. Establish `hpart2 : ∀ (H : Subgroup G) [H.Normal], Finite (G ⧸ H) → Group.IsSolvable (G ⧸ H) → (∀ v, τ v ∈ H) → IrredOn ρ H`. Introduce `H hHn hfin hsolv hτH W hW`.

Take `⟨v₀, q₀, hq₀i, hq₀f, hq₀p, hN2, hN3⟩` from `hG6`. Establish `hpc : q₀.natDegree ∈ (σ v₀).cycleType` using `mem_cycleType_of_factor (hpoly v₀) (hr v₀) (hrf v₀) (hσ v₀) q₀ hq₀i hq₀f hq₀p`. Establish `hN8 : 8 ≤ N`. Establish `h2` using `hq₀p.two_le`. Establish `h5 : 5 ≤ q₀.natDegree`.

Break down `(show q₀.natDegree = 2 ∨ q₀.natDegree = 3 ∨ q₀.natDegree = 4 ∨ 5 ≤ q₀.natDegree by omega) with h | h | h | h` into its components or cases. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Conclude with `absurd (h ▸ hq₀p) (by norm_num)`. Conclude with `h`.

Use linear arithmetic over natural numbers and integers. Set `ρΓ : Representation (Fbar ℓ) ρ.range (Fin N → Fbar ℓ)` to `repGL.comp ρ.range.subtype`. Establish `hρΓ : ∀ (y : ρ.range) x, ρΓ y x = repGL (y : GL (Fin N) (Fbar ℓ)) x` using `fun _ _ => rfl`. Establish `hinjΓ : Function.Injective ρΓ` using `fun a b h => Subtype.ext (repGL_injective h)`. Set `H' : Subgroup ρ.range` to `H.map ρ.rangeRestrict`.

Establish `hH' : H'.Normal` using `hHn.map _ ρ.rangeRestrict_surjective`. Establish `hle : H ≤ H'.comap ρ.rangeRestrict` using `fun h hh => Subgroup.mem_map_of_mem _ hh`. Set `ψ` to `QuotientGroup.map H H' ρ.rangeRestrict hle`. Establish `hψ : Function.Surjective ψ`. Introduce `y`.

Take `⟨z, rfl⟩` from `QuotientGroup.mk_surjective y`. Take `⟨x, rfl⟩` from `ρ.rangeRestrict_surjective z`. Conclude with `⟨QuotientGroup.mk x, rfl⟩`. Establish `hfin' : Finite (ρ.range ⧸ H')` using `Finite.of_surjective ψ hψ`. Establish `hsolv' : Group.IsSolvable (ρ.range ⧸ H')` using `Group.isSolvable_of_surjective hψ`.

Set `T : ρ.range` to `ρ.rangeRestrict (τ v₀)`. Set `Φ : ρ.range` to `ρ.rangeRestrict (φ v₀)`. Establish `hTΦ : Φ * T * Φ⁻¹ = T ^ (g i)` using `by show ρ.rangeRestrict (φ v₀) * ρ.rangeRestrict (τ v₀) * (ρ.rangeRestrict (φ v₀))⁻¹ = ρ.rangeRestrict (τ v₀) ^ (g i)`. Rewrite using `[← map_inv, ← map_mul, ← map_mul, ← map_pow]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, hconj v₀, map_pow]`. Establish `hev : ∀ j, (repGL (ρ (τ v₀))).HasEigenvalue (L v₀ j)`. Introduce `j`. Rewrite using `[Module.End.hasEigenvalue_iff_isRoot_charpoly, charpoly_repGL]`. Establish `: L v₀ j ∈ (ρ (τ v₀) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly.roots`.

Rewrite using `[hroots v₀]`. Conclude with `Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)`. Conclude with `(mem_roots (Matrix.charpoly_monic _).ne_zero).mp this`. Use `choose w hw using fun j => (hev j).exists_hasEigenvector`. Establish `hli : LinearIndependent (Fbar ℓ) w` using `Module.End.eigenvectors_linearIndependent' _ (L v₀) (hLinj v₀) w hw`.

Set `e : Module.Basis (Fin N) (Fbar ℓ) (Fin N → Fbar ℓ)` to `basisOfLinearIndependentOfCardEqFinrank' w hli (by rw [Module.finrank_fintype_fun_eq_card])`. Establish `he : ∀ j, e j = w j` using `fun j => by simp [e]`. Establish `hTpow : ∀ (n : ℕ) j, ρΓ (T ^ n) (e j) = L v₀ j ^ n • e j`. Introduce `n j`. Rewrite using `[map_pow, he]`.

Conclude with `(hw j).pow_apply n`. Establish `hlfin : ∀ j, IsOfFinOrder (L v₀ j)` using `fun j => (ι v₀).isOfFinOrder (primeToPart_isOfFinOrder ℓ _ (hrfin v₀ j))`. Establish `hMo : 0 < ∏ j, orderOf (L v₀ j)` using `Finset.prod_pos (fun j _ => (hlfin j).orderOf_pos)`. Establish `hlM : ∀ j, L v₀ j ^ (∏ j, orderOf (L v₀ j)) = 1` using `fun j => orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))`. Establish `hTfin : IsOfFinOrder T`.

Rewrite using `[isOfFinOrder_iff_pow_eq_one]`. Use `⟨_, hMo, hinjΓ ?_⟩` and prove the remaining obligations. Rewrite using `[map_one]`. Conclude with `e.ext (fun j => by rw [hTpow, hlM, one_smul]; rfl)`. Set `I : Subgroup ρ.range` to `Subgroup.zpowers T`.

Establish `hInat : ∀ y ∈ I, ∃ n : ℕ, T ^ n = y` using `fun y hy => (Submonoid.mem_powers_iff _ _).mp (hTfin.mem_powers_iff_mem_zpowers.mpr hy)`. Establish `hconjI : ∀ y ∈ I, Φ * y * Φ⁻¹ ∈ I`. Introduce `y hy`. Take `⟨n, rfl⟩` from `hInat y hy`. Rewrite using `[← conj_pow, hTΦ, ← pow_mul]`.

Conclude with `Subgroup.npow_mem_zpowers _ _`. Establish `hIfin : Finite I`. Establish `hsub : (I : Set ρ.range) ⊆ Set.range (fun n : Fin (orderOf T) => T ^ (n : ℕ))`. Introduce `y hy`. Take `⟨n, rfl⟩` from `hInat y hy`.

Conclude with `⟨⟨n % orderOf T, Nat.mod_lt _ hTfin.orderOf_pos⟩, pow_mod_orderOf T n⟩`. Conclude with `((Set.finite_range _).subset hsub).to_subtype`. Establish `hIiff : ∀ y, y ∈ I ↔ Φ * y * Φ⁻¹ ∈ I`. Introduce `y`. Use `⟨hconjI y, fun hy => ?_⟩` and prove the remaining obligations.

Set `c : I → I` to `fun z => ⟨Φ * z * Φ⁻¹, hconjI z z.2⟩`. Establish `hc : Function.Injective c`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Subtype.val hab` as an intermediate fact.

Simplify `this` using `[c]`. Take `⟨z, hz⟩` from `(Finite.injective_iff_surjective.mp hc) ⟨_, hy⟩`. Establish `hzy : (z : ρ.range) = y`. Use `congrArg Subtype.val hz` as an intermediate fact. Simplify `this` using `[c]`.

Conclude with `hzy ▸ z.2`. Set `χ' : Fin N → ρ.range → Fbar ℓ` to `fun j y => e.repr (ρΓ y (e j)) j`. Establish `hχpow : ∀ j (n : ℕ), χ' j (T ^ n) = L v₀ j ^ n`. Introduce `j n`. Use `show e.repr (ρΓ (T ^ n) (e j)) j = _`.

Rewrite using `[hTpow]`. Simplify using the standard rewrite rules. Use `hR ρ.range (Fbar ℓ) (Fin N → Fbar ℓ) ρΓ N H' I e χ' Φ (σ v₀)⁻¹ q₀.natDegree hN8 hfin' hsolv' ?_ ?_ ?_ ?_ hIiff ?_ hq₀p (by rw [Fintype.card_fin]; exact hN2) hN3 (by rw [Equiv.Perm.cycleType_inv]; exact hpc) W ?_` and prove the remaining obligations. Conclude with `(Subgroup.zpowers_le).mpr (Subgroup.mem_map_of_mem _ (hτH v₀))`. Introduce `W' hW'`.

Apply `hirr W'` to reduce the goal to its premises. Introduce `h _ x hx`. Use `hW' (ρ.rangeRestrict h) x hx` as an intermediate fact. Rewrite `this` using `[hρΓ, MonoidHom.coe_rangeRestrict, repGL_apply]`. Then use the resulting hypothesis. Introduce `j y hy`.

Take `⟨n, rfl⟩` from `hInat y hy`. Rewrite using `[hTpow, hχpow]`. Introduce `j k hjk`. Use `⟨T, Subgroup.mem_zpowers T, ?_⟩` and prove the remaining obligations. Establish `h1` using `hχpow j 1`.

Establish `h2` using `hχpow k 1`. Rewrite `h1`, `h2` using `[pow_one, pow_one]`. Rewrite using `[h1, h2]`. Conclude with `fun h => hjk (hLinj v₀ h)`. Introduce `j y hy`.

Establish `hz : Φ⁻¹ * y * Φ ∈ I`. Rewrite using `[hIiff]`. Simplify `hy` using `[mul_assoc]`. Take `⟨n, hn⟩` from `hInat _ hz`. Establish `hy' : y = T ^ (g i * n)`.

Rewrite using `[pow_mul, ← hTΦ, conj_pow, hn]`. Use `group`. Rewrite using `[← hn, hy', hχpow, hχpow, pow_mul, ← hLσ]`. Simplify using the standard rewrite rules. Introduce `h hh x hx`.

Take `⟨h0, hh0, rfl⟩` from `Subgroup.mem_map.mp hh`. Rewrite using `[hρΓ, MonoidHom.coe_rangeRestrict, repGL_apply]`. Conclude with `hW h0 hh0 x hx`. Conclude with `⟨hirr, hpart2, hpart3⟩`.
-/
theorem t1 (hR : Restriction) : IrreducibilityCriterion := by
  intro N g hgf PP J f χ _hBB hgood ℓ hℓf i hℓ G hGg ρ τ φ ι hconj hinj hchar
  classical
  have hℓp : ℓ.Prime := hℓf.out
  have hℓg : ℓ ≠ g i := fun h => hℓ (by rw [h]; exact Set.mem_union_left _ (Set.mem_singleton _))
  obtain ⟨hG1, hG2, hG3, hG4, hG5, hG6⟩ := hgood i
  have hpoly : ∀ v, GoodPoly N (f i v) := fun v => ⟨(hG1 v).1, (hG1 v).2.1, (hG1 v).2.2, hG2 v⟩
  choose r σ hr hrf hσ using fun v => exists_index (hpoly v)
  have hmemr : ∀ v j, r v j ∈ rootsBar (f i v) := by
    intro v j; rw [← hrf v]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
  have hr0 : ∀ v j, r v j ≠ 0 := fun v j => ne_zero_of_mem (hpoly v) (hmemr v j)
  have hrfin : ∀ v j, IsOfFinOrder (r v j) := fun v j => isOfFinOrder_of_index (hσ v) j (hr0 v j)
  set L : PP i → Fin N → Fbar ℓ := fun v j => ι v (primeToPart ℓ (r v j)) with hLdef
  have hptp0 : ∀ v j, primeToPart ℓ (r v j) ≠ 0 := by
    intro v j; unfold primeToPart; exact pow_ne_zero _ (hr0 v j)
  have hptpc : ∀ v j, (orderOf (primeToPart ℓ (r v j))).Coprime ℓ :=
    fun v j => primeToPart_coprime hℓp _ (hrfin v j)
  have hLinj : ∀ v, Function.Injective (L v) := by
    intro v j k h
    have h1 := hinj v _ _ (hptp0 v j) (hptp0 v k) (hptpc v j) (hptpc v k) h
    exact hr v (hG3 ℓ hℓp hℓ v _ (hmemr v j) _ (hmemr v k) h1)
  have hLσ : ∀ v j, L v (σ v j) = L v j ^ (g i) := by
    intro v j
    show ι v (primeToPart ℓ (r v (σ v j))) = ι v (primeToPart ℓ (r v j)) ^ (g i)
    rw [hσ v j, primeToPart_pow, map_pow]
    exact orderOf_injective (frobenius (Fbar (g i)) (g i)).toMonoidHom (frobenius_inj _ _) (r v j)
  have hroots : ∀ v, (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly.roots =
      Finset.univ.val.map (L v) := by
    intro v
    have hcp : (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly =
        ((Finset.univ.val.map (L v)).map fun a => X - C a).prod := by
      rw [hchar v, ← hrf v, Multiset.map_map, Multiset.map_map]; rfl
    rw [hcp, roots_multiset_prod_X_sub_C]

  have hirr : IrredOn ρ ⊤ := by
    intro W hW
    refine Formalism.GaloisIrreducibility.irred (Fbar ℓ) (Fin N → Fbar ℓ) (PP i) (Finset (Fbar ℓ))
      (fun v => repGL (ρ (τ v))) (fun v => glEquiv (ρ (φ v))) (fun _ => g i)
      (fun _ S => S) (fun v => blocks (σ v) (L v)) ?_ ?_ ?_ ?_ W ?_ ?_
    · intro v x
      show repGL (ρ (φ v)) (repGL (ρ (τ v)) x) = (repGL (ρ (τ v)) ^ g i) (repGL (ρ (φ v)) x)
      have heq : ρ (φ v) * ρ (τ v) = ρ (τ v) ^ g i * ρ (φ v) := by
        have h := hconj v
        rw [map_mul, map_mul, map_inv] at h
        rw [← h, inv_mul_cancel_right]
      rw [← map_pow, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul repGL, ← map_mul repGL, heq]
    · intro v S hS; exact isOrbit_of_mem (hLσ v) hS
    · intro v
      show (LinearMap.charpoly (repGL (ρ (τ v)))).roots = _
      rw [charpoly_repGL, hroots v, sum_blocks (hLinj v)]
    · intro a ha h2a
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2a
      obtain ⟨v, hv⟩ := hG5 a ha h2a
      refine ⟨v, fun hs => hv ?_⟩
      obtain ⟨A, hA, hAc⟩ := stable_of_subSum (hLinj v) hs
      obtain ⟨Q, -, hQf, hQd, -⟩ := exists_dvd (hpoly v) (hrf v) (hσ v) A hA
      exact ⟨Q, hQf, hQd.trans hAc⟩
    · intro v x hx
      show repGL (ρ (τ v)) x ∈ W
      rw [repGL_apply]; exact hW _ (Subgroup.mem_top _) x hx
    · intro v x hx
      show glEquiv (ρ (φ v)) x ∈ W
      rw [glEquiv_apply, repGL_apply]; exact hW _ (Subgroup.mem_top _) x hx

  have hpart3 : ∀ v j, ¬ (Matrix.charpoly (ρ (τ v) : Matrix (Fin N) (Fin N) (Fbar ℓ))).IsRoot
      (ι v (primeToPart ℓ (algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i))))) := by
    intro v j hroot
    have hmem := (mem_roots (Matrix.charpoly_monic _).ne_zero).mpr hroot
    rw [hroots v] at hmem
    obtain ⟨k, -, hk⟩ := Multiset.mem_map.mp hmem
    have hc0 : algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i)) ≠ 0 :=
      (_root_.map_ne_zero _).mpr (χ i v j).ne_zero
    have hcfin : IsOfFinOrder (algebraMap (ZMod (g i)) (Fbar (g i)) (χ i v j : ZMod (g i))) :=
      MonoidHom.isOfFinOrder ((algebraMap (ZMod (g i)) (Fbar (g i))).toMonoidHom.comp (Units.coeHom _))
        (isOfFinOrder_of_finite (χ i v j))
    have h1 := hinj v _ _ (hptp0 v k) (by unfold primeToPart; exact pow_ne_zero _ hc0)
      (hptpc v k) (primeToPart_coprime hℓp _ hcfin) hk
    exact hG4 ℓ hℓp hℓg v j _ (hmemr v k) h1

  have hpart2 : ∀ (H : Subgroup G) [H.Normal], Finite (G ⧸ H) → Group.IsSolvable (G ⧸ H) →
      (∀ v, τ v ∈ H) → IrredOn ρ H := by
    intro H hHn hfin hsolv hτH W hW
    obtain ⟨v₀, q₀, hq₀i, hq₀f, hq₀p, hN2, hN3⟩ := hG6
    have hpc : q₀.natDegree ∈ (σ v₀).cycleType :=
      mem_cycleType_of_factor (hpoly v₀) (hr v₀) (hrf v₀) (hσ v₀) q₀ hq₀i hq₀f hq₀p
    have hN8 : 8 ≤ N := by
      have h2 := hq₀p.two_le
      have h5 : 5 ≤ q₀.natDegree := by
        rcases (show q₀.natDegree = 2 ∨ q₀.natDegree = 3 ∨ q₀.natDegree = 4 ∨
          5 ≤ q₀.natDegree by omega) with h | h | h | h
        · omega
        · omega
        · exact absurd (h ▸ hq₀p) (by norm_num)
        · exact h
      omega
    let ρΓ : Representation (Fbar ℓ) ρ.range (Fin N → Fbar ℓ) := repGL.comp ρ.range.subtype
    have hρΓ : ∀ (y : ρ.range) x, ρΓ y x = repGL (y : GL (Fin N) (Fbar ℓ)) x := fun _ _ => rfl
    have hinjΓ : Function.Injective ρΓ := fun a b h => Subtype.ext (repGL_injective h)
    let H' : Subgroup ρ.range := H.map ρ.rangeRestrict
    have hH' : H'.Normal := hHn.map _ ρ.rangeRestrict_surjective
    have hle : H ≤ H'.comap ρ.rangeRestrict := fun h hh => Subgroup.mem_map_of_mem _ hh
    let ψ := QuotientGroup.map H H' ρ.rangeRestrict hle
    have hψ : Function.Surjective ψ := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨x, rfl⟩ := ρ.rangeRestrict_surjective z
      exact ⟨QuotientGroup.mk x, rfl⟩
    have hfin' : Finite (ρ.range ⧸ H') := Finite.of_surjective ψ hψ
    have hsolv' : Group.IsSolvable (ρ.range ⧸ H') := Group.isSolvable_of_surjective hψ
    let T : ρ.range := ρ.rangeRestrict (τ v₀)
    let Φ : ρ.range := ρ.rangeRestrict (φ v₀)
    have hTΦ : Φ * T * Φ⁻¹ = T ^ (g i) := by
      show ρ.rangeRestrict (φ v₀) * ρ.rangeRestrict (τ v₀) * (ρ.rangeRestrict (φ v₀))⁻¹ =
        ρ.rangeRestrict (τ v₀) ^ (g i)
      rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
      apply Subtype.ext
      rw [MonoidHom.coe_rangeRestrict, MonoidHom.coe_rangeRestrict, hconj v₀, map_pow]

    have hev : ∀ j, (repGL (ρ (τ v₀))).HasEigenvalue (L v₀ j) := by
      intro j
      rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, charpoly_repGL]
      have : L v₀ j ∈ (ρ (τ v₀) : Matrix (Fin N) (Fin N) (Fbar ℓ)).charpoly.roots := by
        rw [hroots v₀]; exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val j)
      exact (mem_roots (Matrix.charpoly_monic _).ne_zero).mp this
    choose w hw using fun j => (hev j).exists_hasEigenvector
    have hli : LinearIndependent (Fbar ℓ) w :=
      Module.End.eigenvectors_linearIndependent' _ (L v₀) (hLinj v₀) w hw
    let e : Module.Basis (Fin N) (Fbar ℓ) (Fin N → Fbar ℓ) :=
      basisOfLinearIndependentOfCardEqFinrank' w hli (by rw [Module.finrank_fintype_fun_eq_card])
    have he : ∀ j, e j = w j := fun j => by simp [e]
    have hTpow : ∀ (n : ℕ) j, ρΓ (T ^ n) (e j) = L v₀ j ^ n • e j := by
      intro n j
      rw [map_pow, he]
      exact (hw j).pow_apply n
    have hlfin : ∀ j, IsOfFinOrder (L v₀ j) :=
      fun j => (ι v₀).isOfFinOrder (primeToPart_isOfFinOrder ℓ _ (hrfin v₀ j))
    have hMo : 0 < ∏ j, orderOf (L v₀ j) := Finset.prod_pos (fun j _ => (hlfin j).orderOf_pos)
    have hlM : ∀ j, L v₀ j ^ (∏ j, orderOf (L v₀ j)) = 1 := fun j =>
      orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
    have hTfin : IsOfFinOrder T := by
      rw [isOfFinOrder_iff_pow_eq_one]
      refine ⟨_, hMo, hinjΓ ?_⟩
      rw [map_one]
      exact e.ext (fun j => by rw [hTpow, hlM, one_smul]; rfl)
    let I : Subgroup ρ.range := Subgroup.zpowers T
    have hInat : ∀ y ∈ I, ∃ n : ℕ, T ^ n = y := fun y hy =>
      (Submonoid.mem_powers_iff _ _).mp (hTfin.mem_powers_iff_mem_zpowers.mpr hy)
    have hconjI : ∀ y ∈ I, Φ * y * Φ⁻¹ ∈ I := by
      intro y hy
      obtain ⟨n, rfl⟩ := hInat y hy
      rw [← conj_pow, hTΦ, ← pow_mul]
      exact Subgroup.npow_mem_zpowers _ _
    have hIfin : Finite I := by
      have hsub : (I : Set ρ.range) ⊆ Set.range (fun n : Fin (orderOf T) => T ^ (n : ℕ)) := by
        intro y hy
        obtain ⟨n, rfl⟩ := hInat y hy
        exact ⟨⟨n % orderOf T, Nat.mod_lt _ hTfin.orderOf_pos⟩, pow_mod_orderOf T n⟩
      exact ((Set.finite_range _).subset hsub).to_subtype
    have hIiff : ∀ y, y ∈ I ↔ Φ * y * Φ⁻¹ ∈ I := by
      intro y
      refine ⟨hconjI y, fun hy => ?_⟩
      let c : I → I := fun z => ⟨Φ * z * Φ⁻¹, hconjI z z.2⟩
      have hc : Function.Injective c := by
        intro a b hab
        apply Subtype.ext
        have := congrArg Subtype.val hab
        simpa [c] using this
      obtain ⟨z, hz⟩ := (Finite.injective_iff_surjective.mp hc) ⟨_, hy⟩
      have hzy : (z : ρ.range) = y := by
        have := congrArg Subtype.val hz
        simpa [c] using this
      exact hzy ▸ z.2
    let χ' : Fin N → ρ.range → Fbar ℓ := fun j y => e.repr (ρΓ y (e j)) j
    have hχpow : ∀ j (n : ℕ), χ' j (T ^ n) = L v₀ j ^ n := by
      intro j n
      show e.repr (ρΓ (T ^ n) (e j)) j = _
      rw [hTpow]
      simp
    refine hR ρ.range (Fbar ℓ) (Fin N → Fbar ℓ) ρΓ N H' I e χ' Φ (σ v₀)⁻¹ q₀.natDegree hN8
      hfin' hsolv' ?_ ?_ ?_ ?_ hIiff ?_ hq₀p (by rw [Fintype.card_fin]; exact hN2) hN3
      (by rw [Equiv.Perm.cycleType_inv]; exact hpc) W ?_
    · exact (Subgroup.zpowers_le).mpr (Subgroup.mem_map_of_mem _ (hτH v₀))
    · intro W' hW'
      apply hirr W'
      intro h _ x hx
      have := hW' (ρ.rangeRestrict h) x hx
      rwa [hρΓ, MonoidHom.coe_rangeRestrict, repGL_apply] at this
    · intro j y hy
      obtain ⟨n, rfl⟩ := hInat y hy
      rw [hTpow, hχpow]
    · intro j k hjk
      refine ⟨T, Subgroup.mem_zpowers T, ?_⟩
      have h1 := hχpow j 1
      have h2 := hχpow k 1
      rw [pow_one, pow_one] at h1 h2
      rw [h1, h2]
      exact fun h => hjk (hLinj v₀ h)
    · intro j y hy
      have hz : Φ⁻¹ * y * Φ ∈ I := by
        rw [hIiff]; simpa [mul_assoc] using hy
      obtain ⟨n, hn⟩ := hInat _ hz
      have hy' : y = T ^ (g i * n) := by
        rw [pow_mul, ← hTΦ, conj_pow, hn]; group
      rw [← hn, hy', hχpow, hχpow, pow_mul, ← hLσ]
      simp
    · intro h hh x hx
      obtain ⟨h0, hh0, rfl⟩ := Subgroup.mem_map.mp hh
      rw [hρΓ, MonoidHom.coe_rangeRestrict, repGL_apply]
      exact hW h0 hh0 x hx
  exact ⟨hirr, hpart2, hpart3⟩

end Formalism.CyclotomicNorms.CycleTypeFiniteOrder

/- English proof (translation)
The claim follows from `Formalism.CyclotomicNorms.CycleTypeFiniteOrder.t1 hR`.
-/
theorem Formalism.CyclotomicNorms.irreducibility_of_restriction (hR : Formalism.CyclotomicNorms.Restriction) : Formalism.CyclotomicNorms.IrreducibilityCriterion :=
  Formalism.CyclotomicNorms.CycleTypeFiniteOrder.t1 hR
