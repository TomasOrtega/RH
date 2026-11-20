import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DcSumEqOfMk
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.GlintPrincRelIndexNeZero

open NumberField IsDedekindDomain IsLocalRing UpperTheory.V UpperTheory.V.Sd Formalism.L2.Host

section Gen

variable {O K : Type} [CommRing O] [IsLocalRing O] [Field K]

private def KK (φ : O →+* K) (n : ℕ) : Subgroup (GL (Fin 2) K) :=
  ((mirab _).comap (Matrix.GeneralLinearGroup.map (n := Fin 2)
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n)))).map (Matrix.GeneralLinearGroup.map φ)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Assume the hypotheses and unpack their components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
private theorem mem_KK (φ : O →+* K) (n : ℕ) (g : GL (Fin 2) K) :
    g ∈ KK φ n ↔ ∃ a b c d : O, (g : Matrix (Fin 2) (Fin 2) K) = !![φ a, φ b; φ c, φ d] ∧
      IsUnit (a * d - b * c) ∧ c ∈ maximalIdeal O ^ n ∧ d - 1 ∈ maximalIdeal O ^ n := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    refine ⟨h 0 0, h 0 1, h 1 0, h 1 1, ?_, ?_, ?_, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> rfl
    · have := (Matrix.GeneralLinearGroup.det h).isUnit
      rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at this
    · have h0 := congrFun hh 0
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
    · have h0 := congrFun hh 1
      rw [← Ideal.Quotient.eq, map_one]
      simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using h0
  · rintro ⟨a, b, c, d, hg, hu, hc, hd⟩
    have hu' : IsUnit (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) O) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]; exact hu
    obtain ⟨h, hh⟩ := hu'
    refine ⟨h, ?_, ?_⟩
    · change Matrix.vecMul ![0, 1] ((h : Matrix (Fin 2) (Fin 2) O).map
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) = ![0, 1]
      rw [hh]
      rw [← Ideal.Quotient.eq_zero_iff_mem] at hc
      rw [← Ideal.Quotient.eq, map_one] at hd
      ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hc, hd]
    · apply Units.ext
      change (h : Matrix (Fin 2) (Fin 2) O).map φ = g
      rw [hh, hg]
      ext i j; fin_cases i <;> fin_cases j <;> rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
private theorem coset_iff (φ : O →+* K) (n : ℕ) (y z : GL (Fin 2) K) :
    (y : GL (Fin 2) K ⧸ KK φ n) = z ↔ ∃ a b c d : O,
      (y : Matrix (Fin 2) (Fin 2) K) * !![φ a, φ b; φ c, φ d] = z ∧
      IsUnit (a * d - b * c) ∧ c ∈ maximalIdeal O ^ n ∧ d - 1 ∈ maximalIdeal O ^ n := by
  rw [QuotientGroup.eq, mem_KK]
  refine exists₄_congr fun a b c d => and_congr_left' ?_
  rw [Units.val_mul, Units.inv_mul_eq_iff_eq_mul, eq_comm]

/- English proof (translation)
Supply the required witnesses or components.
-/
private theorem orbit_iff (φ : O →+* K) (n : ℕ) (x : GL (Fin 2) K) (q : GL (Fin 2) K ⧸ KK φ n) :
    q ∈ MulAction.orbit (KK φ n) (x : GL (Fin 2) K ⧸ KK φ n) ↔
      ∃ k ∈ KK φ n, ((k * x : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n) = q :=
  ⟨fun ⟨k, hk⟩ => ⟨k.1, k.2, hk⟩, fun ⟨k, hk, h⟩ => ⟨⟨k, hk⟩, h⟩⟩

private def zz (π : Kˣ) : GL (Fin 2) K := Matrix.GeneralLinearGroup.scalar (Fin 2) π * (aff π 0)⁻¹

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem aff_val (π : Kˣ) (u : K) : (aff π u : Matrix (Fin 2) (Fin 2) K) = !![(π : K), u; 0, 1] := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem zz_val (π : Kˣ) : (zz π : Matrix (Fin 2) (Fin 2) K) = !![1, 0; 0, (π : K)] := by
  rw [zz, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, aff_val]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
private theorem y_mem (φ : O →+* K) (n : ℕ) (π : Kˣ) (u : O) :
    ((aff π (φ u) : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n) ∈
      MulAction.orbit (KK φ n) ((aff π 0 : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n) := by
  rw [orbit_iff]
  refine ⟨aff 1 (φ u), (mem_KK _ _ _).2 ⟨1, u, 0, 1, by simp [aff_val], by simp, by simp, by simp⟩, ?_⟩
  congr 1
  apply Units.ext
  rw [Units.val_mul]
  simp [aff_val]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem z_mem (φ : O →+* K) (π : Kˣ) :
    ((zz π : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ 0) ∈
      MulAction.orbit (KK φ 0) ((aff π 0 : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ 0) := by
  rw [orbit_iff]
  have hu' : IsUnit (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_two_of]; simp
  obtain ⟨s, hs⟩ := hu'
  refine ⟨s, (mem_KK _ _ _).2 ⟨0, 1, 1, 0, by simp [hs], by simp, by simp, by simp⟩, ?_⟩
  refine (coset_iff _ _ _ _).2 ⟨0, 1, 1, 0, ?_, by simp, by simp, by simp⟩
  rw [Units.val_mul, hs, zz_val, aff_val]
  simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Substitute using the available equality. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation. Apply an available result and prove the equalities needed to match it to the conclusion. Expand and normalize the polynomial expressions, which then agree.

A detailed English derivation is pending.
-/
private theorem cover (φ : O →+* K) (n : ℕ) (π : Kˣ) (p : O) (hp : φ p = π)
    (hm : maximalIdeal O = Ideal.span {p}) (S : Finset O)
    (hS : Set.SurjOn (residue O) (S : Set O) Set.univ) (q : GL (Fin 2) K ⧸ KK φ n)
    (hq : q ∈ MulAction.orbit (KK φ n) ((aff π 0 : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n)) :
    (∃ u ∈ S, ((aff π (φ u) : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n) = q) ∨
      (n = 0 ∧ ((zz π : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n) = q) := by
  obtain ⟨k, hk, rfl⟩ := (orbit_iff _ _ _ _).1 hq
  obtain ⟨a, b, c, d, hg, hu, hc, hd⟩ := (mem_KK _ _ _).1 hk
  by_cases hdu : IsUnit d
  · left
    obtain ⟨e, he⟩ := hdu.exists_left_inv
    obtain ⟨u, huS, hue⟩ := hS (Set.mem_univ (residue O (b * e)))
    have h1 : b * e - u ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, map_sub, hue, sub_self]
    rw [hm, Ideal.mem_span_singleton'] at h1
    obtain ⟨t, ht⟩ := h1
    have hb : b = p * (t * d) + u * d := by linear_combination (-d) * ht - b * he
    refine ⟨u, huS, (coset_iff _ _ _ _).2 ⟨a - u * c, t * d, c * p, d, ?_, ?_, Ideal.mul_mem_right _ _ hc, hd⟩⟩
    · rw [Units.val_mul, hg, aff_val, aff_val, ← hp, hb]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · convert hu using 1
      rw [hb]; ring
  · right
    have hdm : d ∈ maximalIdeal O := hdu
    have hn : n = 0 := by
      by_contra hn
      have h1 : d - 1 ∈ maximalIdeal O := Ideal.pow_le_self hn hd
      have h2 := Ideal.sub_mem _ hdm h1
      simp at h2
    subst hn
    rw [hm, Ideal.mem_span_singleton'] at hdm
    obtain ⟨t, rfl⟩ := hdm
    refine ⟨rfl, (coset_iff _ _ _ _).2 ⟨a * p, b, c, t, ?_, ?_, by simp, by simp⟩⟩
    · rw [Units.val_mul, hg, aff_val, zz_val, ← hp]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · convert hu using 1
      ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
private theorem yy_res (φ : O →+* K) (hφ : Function.Injective φ) (n : ℕ) (π : Kˣ) (p : O) (hp : φ p = π)
    (hm : p ∈ maximalIdeal O) (u u' : O)
    (h : ((aff π (φ u) : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n) = (aff π (φ u') : GL (Fin 2) K)) :
    residue O u = residue O u' := by
  obtain ⟨a, b, c, d, hg, -⟩ := (coset_iff _ _ _ _).1 h
  rw [aff_val, aff_val, ← hp] at hg
  have h1 := congrFun (congrFun hg 0) 1
  have h2 := congrFun (congrFun hg 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h1 h2
  have h3 : p * b + u = u' := hφ (by rw [map_add, map_mul, ← h1, h2, mul_one])
  rw [← h3, map_add, map_mul, (residue_eq_zero_iff _).2 hm, zero_mul, zero_add]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem yz_ne (φ : O →+* K) (hφ : Function.Injective φ) (n : ℕ) (π : Kˣ) (p : O) (hp : φ p = π)
    (hm : p ∈ maximalIdeal O) (u : O) :
    ((aff π (φ u) : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n) ≠ (zz π : GL (Fin 2) K) := by
  intro h
  obtain ⟨a, b, c, d, hg, -⟩ := (coset_iff _ _ _ _).1 h
  rw [aff_val, zz_val, ← hp] at hg
  have h1 := congrFun (congrFun hg 0) 0
  have h2 := congrFun (congrFun hg 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h1 h2
  have h3 : p * a = 1 := hφ (by rw [map_mul, map_one, ← h1, h2, mul_zero, add_zero])
  exact hm (IsUnit.of_mul_eq_one a h3)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Equip the data with the indicated structure. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Separate the alternatives or extract the components of the hypothesis. Prove the second alternative. Prove the first alternative. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Separate the alternatives or extract the components of the hypothesis. Both sides reduce to the same expression. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem gen (φ : O →+* K) (hφ : Function.Injective φ) [Finite (ResidueField O)] (n : ℕ) (π : Kˣ) (p : O)
    (hp : φ p = π) (hm : maximalIdeal O = Ideal.span {p}) (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin 2) K) V) (v : V) (hv : v ∈ Hi.fixd ρ (KK φ n)) :
    Hi.dc ρ (KK φ n) (KK φ n) (aff π 0) v ∈ Hi.fixd ρ (KK φ n) ∧
    ∀ S : Finset O, Set.BijOn (residue O) (S : Set O) Set.univ →
      Hi.dc ρ (KK φ n) (KK φ n) (aff π 0) v = ∑ u ∈ S, ρ (aff π (φ u)) v + if n = 0 then ρ (zz π) v else 0 := by
  classical
  have hpm : p ∈ maximalIdeal O := by rw [hm]; exact Ideal.mem_span_singleton_self p
  have hfin : (MulAction.orbit (KK φ n) ((aff π 0 : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n)).Finite := by
    letI := Fintype.ofFinite (ResidueField O)
    choose s hs using (residue_surjective (R := O))
    have hS : Set.SurjOn (residue O) ((Finset.univ.image s : Finset O) : Set O) Set.univ :=
      fun r _ => ⟨s r, by simp, hs r⟩
    refine ((((Finset.univ.image s).finite_toSet).image
      fun u => ((aff π (φ u) : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n)).insert
        ((zz π : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n)).subset fun q hq => ?_
    rcases cover φ n π p hp hm _ hS q hq with ⟨u, hu, h⟩ | ⟨-, h⟩
    · exact Or.inr ⟨u, hu, h⟩
    · exact Or.inl h.symm
  obtain ⟨h1, h2, -⟩ := Hi.dcSum ℂ _ V ρ (KK φ n) (KK φ n) (aff π 0) hfin
  refine ⟨h2 v hv, fun S hS => ?_⟩
  have hinj : ∀ u ∈ S, ∀ u' ∈ S, ((aff π (φ u) : GL (Fin 2) K) : GL (Fin 2) K ⧸ KK φ n) =
      (aff π (φ u') : GL (Fin 2) K) → u = u' := fun u hu u' hu' h =>
    hS.injOn hu hu' (yy_res φ hφ n π p hp hpm u u' h)
  have hsum : ∑ y ∈ S.image (fun u => aff π (φ u)), ρ y v = ∑ u ∈ S, ρ (aff π (φ u)) v :=
    Finset.sum_image fun u hu u' hu' h => hinj u hu u' hu' (congrArg _ h)
  by_cases hn : n = 0
  · subst hn
    have hz : zz π ∉ S.image (fun u => aff π (φ u)) := by
      intro h
      obtain ⟨u, -, h⟩ := Finset.mem_image.1 h
      exact yz_ne φ hφ 0 π p hp hpm u (congrArg _ h)
    rw [h1 (insert (zz π) (S.image fun u => aff π (φ u))) ?_ ?_ v hv, Finset.sum_insert hz, hsum, if_pos rfl, add_comm]
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact z_mem φ π
      · obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hy
        exact y_mem φ 0 π u
    · intro q hq
      rcases cover φ 0 π p hp hm S hS.surjOn q hq with ⟨u, hu, rfl⟩ | ⟨-, rfl⟩
      · refine ⟨_, ⟨Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hu), rfl⟩, ?_⟩
        rintro y ⟨hy, h⟩
        rcases Finset.mem_insert.1 hy with rfl | hy
        · exact absurd h.symm (yz_ne φ hφ 0 π p hp hpm u)
        · obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
          rw [hinj u' hu' u hu h]
      · refine ⟨_, ⟨Finset.mem_insert_self _ _, rfl⟩, ?_⟩
        rintro y ⟨hy, h⟩
        rcases Finset.mem_insert.1 hy with rfl | hy
        · rfl
        · obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
          exact absurd h (yz_ne φ hφ 0 π p hp hpm u')
  · rw [h1 (S.image fun u => aff π (φ u)) ?_ ?_ v hv, hsum, if_neg hn, add_zero]
    · intro y hy
      obtain ⟨u, -, rfl⟩ := Finset.mem_image.1 hy
      exact y_mem φ n π u
    · intro q hq
      rcases cover φ n π p hp hm S hS.surjOn q hq with ⟨u, hu, rfl⟩ | ⟨h, -⟩
      · refine ⟨_, ⟨Finset.mem_image_of_mem _ hu, rfl⟩, ?_⟩
        rintro y ⟨hy, h⟩
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
        rw [hinj u' hu' u hu h]
      · exact absurd h hn

end Gen

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Rewrite the conclusion using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
private theorem span_unif {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F))
    (p : w.adicCompletionIntegers F) (hp : Valued.v (p : w.adicCompletion F) = WithZero.exp (-1 : ℤ)) :
    maximalIdeal (w.adicCompletionIntegers F) = Ideal.span {p} := by
  have hp0 : (p : w.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  ext x
  rw [Ideal.mem_span_singleton', IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  constructor
  · intro h
    have h1 : Valued.v (x : w.adicCompletion F) < 1 := lt_of_le_of_ne x.2 h
    have h2 : Valued.v (x : w.adicCompletion F) ≤ WithZero.exp (-1 : ℤ) := by
      rcases eq_or_ne (Valued.v (x : w.adicCompletion F)) 0 with h0 | h0
      · rw [h0]; exact zero_le'
      rw [← WithZero.exp_log h0] at h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [WithZero.exp_le_exp]
      omega
    refine ⟨⟨(x : w.adicCompletion F) / p, ?_⟩, Subtype.ext (div_mul_cancel₀ _ hp0)⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hp]
    exact div_le_one_of_le₀ h2 zero_le'
  · rintro ⟨z, rfl⟩ h
    have hz : Valued.v (z : w.adicCompletion F) ≤ 1 := z.2
    have h1 : Valued.v ((z : w.adicCompletion F) * p) ≤ WithZero.exp (-1 : ℤ) := by
      rw [map_mul, hp]; exact mul_le_of_le_one_left' hz
    have h' : Valued.v ((z : w.adicCompletion F) * p) = 1 := h
    rw [h', ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Sd.uopSum :
    UpperTheory.V.Sd.UopSum := by
  intro F _ _ w V _ _ ρ c v hv
  haveI := Formalism.UG.P.glint_finite_residueField w
  have hπ : Valued.v ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    unif_spec w
  have hmem : ((atFin w (unif w) : (w.adicCompletion F)ˣ) : w.adicCompletion F) ∈ w.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hπ, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  exact gen (w.adicCompletionIntegers F).subtype Subtype.val_injective c (atFin w (unif w)) ⟨_, hmem⟩ rfl
    (span_unif w ⟨_, hmem⟩ hπ) V ρ v hv
