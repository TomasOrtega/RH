import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidueFlagPoints.TwWts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.CuspRep GlobalTheory.GalOfCusp

/- English proof (translation)
Use `haveI : Finite (Γ ⧸ U) := U.quotient_finite_of_isOpen hU`. Use `haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Use `⟨U.normalCore.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun s => ?_⟩` and prove the remaining obligations. Conclude with `U.normalCore_le (U.normalCore.pow_index_mem s)`.
-/
private theorem pow_mem_open {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (U : Subgroup Γ) (hU : IsOpen (U : Set Γ)) : ∃ N : ℕ, 0 < N ∧ ∀ s : Γ, s ^ N ∈ U := by
  haveI : Finite (Γ ⧸ U) := U.quotient_finite_of_isOpen hU
  haveI : U.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨U.normalCore.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, fun s => ?_⟩
  exact U.normalCore_le (U.normalCore.pow_index_mem s)

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T c' h K X B n φ hφ y w hw hW`. Use `haveI := T.fin`. Use `haveI : Finite (W.Vl l T.L) := Finite.of_equiv _ K.e.symm`. Use `haveI := Fintype.ofFinite (W.Vl l T.L)`. Take `⟨U, hU, hUψ⟩` from `hW`.

Take `⟨N, hN, hNU⟩` from `pow_mem_open U hU`. Use `choose e k hk he hek using fun v : W.Vl l T.L => Pt.twWts K n (K.s.A v) (by rw [K.hA]; exact T.ovl _)`. Establish `hev : ∀ v i, Even (w i + e v)`. Introduce `v i`. Take `⟨a, ha⟩` from `hw i`.

Take `⟨b, hb⟩` from `he v`. Conclude with `⟨a + b - n, by omega⟩`. Use `⟨fun v i => (w i + e v) / 2, ?_, 2 * N * ∏ v, k v, ?_, ?_⟩` and prove the remaining obligations. Introduce `v i j`. Establish `h1` using `Int.two_mul_ediv_two_of_even (hev v i)`.

Establish `h2` using `Int.two_mul_ediv_two_of_even (hev v j)`. Simplify using `only`. Use linear arithmetic over natural numbers and integers. Conclude with `Nat.mul_pos (Nat.mul_pos two_pos hN) (Finset.prod_pos fun v _ => hk v)`. Introduce `v i g hg`.

Take `⟨q, hq⟩` from `Finset.dvd_prod_of_mem k (Finset.mem_univ v)`. Establish `hm : 2 * ((w i + e v) / 2) = w i + e v` using `Int.two_mul_ediv_two_of_even (hev v i)`. Establish `hgN : ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ∈ Ine (K.s.A v)`. Rewrite using `[Subgroup.coe_pow]`. Conclude with `Subgroup.pow_mem _ hg N`.

Establish `hres : resLe T.F_le ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ∈ U ⊓ Ine (T.pl (K.e v))`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.coe_pow, map_pow]`. Conclude with `hNU _`. Conclude with `(resLe_mem_Ine (A := T.pl (K.e v)) T.F_le).2 (by rw [← K.hA]; exact hgN)`.

Establish `hdec : resLe T.F_le ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ∈ Dec (T.pl (K.e v))` using `(resLe_mem_Dec (A := T.pl (K.e v)) T.F_le).2 (by rw [← K.hA]; exact (g ^ N).2)`. Establish `hval` using `hφ.psi_val y v i (g ^ N) hdec`. Establish `hsq` using `hUψ (K.e v) i _ hres`. Rewrite `hsq` using `[cycBar_resLe]`. Establish `hP : (Link.pt φ y).psi v i (g ^ N) ^ 2 = K.twc n ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ^ 2 * cycBar T.L Ω l ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ^ w i`.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_pow_eq_pow_val, hval, Units.val_mul, ← hsq, Units.val_pow_eq_pow_val]`. Conclude with `mul_pow _ _ _`. Establish `hk1` using `hek v _ hgN`. Use `set p := (Link.pt φ y).psi v i g`.

Use `set t := K.twc n ((g ^ N : Dec (K.s.A v)) : G T.L Ω)`. Use `set cg := cycBar T.L Ω l (g : G T.L Ω)`. Establish `hpN : (Link.pt φ y).psi v i (g ^ N) = p ^ N` using `map_pow _ _ _`. Establish `hcN : cycBar T.L Ω l ((g ^ N : Dec (K.s.A v)) : G T.L Ω) = cg ^ N`. Rewrite using `[Subgroup.coe_pow, map_pow]`.

Rewrite `hP` using `[hpN, hcN]`. Rewrite `hk1` using `[hcN]`. Use `show (p * cg ^ (-((w i + e v) / 2))) ^ (2 * N * ∏ v, k v) = 1`. Use `set m := (w i + e v) / 2`. Establish `h1 : (cg ^ (-m)) ^ N = (cg ^ N) ^ (-m)`.

Rewrite using `[← zpow_natCast, ← zpow_mul, ← zpow_natCast cg N, ← zpow_mul, mul_comm]`. Establish `hx : (p * cg ^ (-m)) ^ (2 * N) = t ^ 2 * (cg ^ N) ^ (-e v)`. Rewrite using `[mul_comm 2 N, pow_mul, mul_pow, h1, mul_pow, hP, ← zpow_natCast ((cg ^ N) ^ (-m)) 2, ← zpow_mul, mul_assoc, ← zpow_add]`. Use `congr 2`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[pow_mul, hx, hq, pow_mul, hk1, one_pow]`.
-/
theorem UpperTheory.V.Ws.Pt.ptWts :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (B : W.UniversalOrdinaryDeterminantRing K.r) (n : ℕ) (φ : B.B →ₐ[c'.O] X.B), K.IsPhi X n B φ → ∀ y : X.A →ₐ[c'.O] PadicAlgCl l, ∀ w : Fin 4 → ℤ, (∀ i, Even (w i + n)) → T.Wts w (X.P.map (y : X.A →+* PadicAlgCl l)) → ∃ m : W.Vl l T.L → Fin 4 → ℤ, (∀ v i j, 2 * (m v i - m v j) = w i - w j) ∧ ∃ k : ℕ, 0 < k ∧ ∀ (v : W.Vl l T.L) (i : Fin 4) (g : Dec (F := T.L) (K.s.A v)), (g : G T.L Ω) ∈ Ine (F := T.L) (K.s.A v) → ((Link.pt φ y).psi v i g * cycBar T.L Ω l g ^ (-m v i)) ^ k = 1 := by
  intro Ω _ _ _ l _ c D T c' h K X B n φ hφ y w hw hW
  haveI := T.fin
  haveI : Finite (W.Vl l T.L) := Finite.of_equiv _ K.e.symm
  haveI := Fintype.ofFinite (W.Vl l T.L)
  obtain ⟨U, hU, hUψ⟩ := hW
  obtain ⟨N, hN, hNU⟩ := pow_mem_open U hU
  choose e k hk he hek using fun v : W.Vl l T.L =>
    Pt.twWts K n (K.s.A v) (by rw [K.hA]; exact T.ovl _)
  have hev : ∀ v i, Even (w i + e v) := by
    intro v i
    obtain ⟨a, ha⟩ := hw i
    obtain ⟨b, hb⟩ := he v
    exact ⟨a + b - n, by omega⟩
  refine ⟨fun v i => (w i + e v) / 2, ?_, 2 * N * ∏ v, k v, ?_, ?_⟩
  · intro v i j
    have h1 := Int.two_mul_ediv_two_of_even (hev v i)
    have h2 := Int.two_mul_ediv_two_of_even (hev v j)
    simp only
    omega
  · exact Nat.mul_pos (Nat.mul_pos two_pos hN) (Finset.prod_pos fun v _ => hk v)
  · intro v i g hg
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem k (Finset.mem_univ v)
    have hm : 2 * ((w i + e v) / 2) = w i + e v := Int.two_mul_ediv_two_of_even (hev v i)
    have hgN : ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ∈ Ine (K.s.A v) := by
      rw [Subgroup.coe_pow]
      exact Subgroup.pow_mem _ hg N
    have hres : resLe T.F_le ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ∈ U ⊓ Ine (T.pl (K.e v)) := by
      refine ⟨?_, ?_⟩
      · rw [Subgroup.coe_pow, map_pow]
        exact hNU _
      · exact (resLe_mem_Ine (A := T.pl (K.e v)) T.F_le).2 (by rw [← K.hA]; exact hgN)
    have hdec : resLe T.F_le ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ∈ Dec (T.pl (K.e v)) :=
      (resLe_mem_Dec (A := T.pl (K.e v)) T.F_le).2 (by rw [← K.hA]; exact (g ^ N).2)
    have hval := hφ.psi_val y v i (g ^ N) hdec
    have hsq := hUψ (K.e v) i _ hres
    rw [cycBar_resLe] at hsq
    have hP : (Link.pt φ y).psi v i (g ^ N) ^ 2 =
        K.twc n ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ^ 2 *
          cycBar T.L Ω l ((g ^ N : Dec (K.s.A v)) : G T.L Ω) ^ w i := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hval, Units.val_mul, ← hsq, Units.val_pow_eq_pow_val]
      exact mul_pow _ _ _
    have hk1 := hek v _ hgN
    set p := (Link.pt φ y).psi v i g
    set t := K.twc n ((g ^ N : Dec (K.s.A v)) : G T.L Ω)
    set cg := cycBar T.L Ω l (g : G T.L Ω)
    have hpN : (Link.pt φ y).psi v i (g ^ N) = p ^ N := map_pow _ _ _
    have hcN : cycBar T.L Ω l ((g ^ N : Dec (K.s.A v)) : G T.L Ω) = cg ^ N := by
      rw [Subgroup.coe_pow, map_pow]
    rw [hpN, hcN] at hP
    rw [hcN] at hk1
    show (p * cg ^ (-((w i + e v) / 2))) ^ (2 * N * ∏ v, k v) = 1
    set m := (w i + e v) / 2
    have h1 : (cg ^ (-m)) ^ N = (cg ^ N) ^ (-m) := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_natCast cg N, ← zpow_mul, mul_comm]
    have hx : (p * cg ^ (-m)) ^ (2 * N) = t ^ 2 * (cg ^ N) ^ (-e v) := by
      rw [mul_comm 2 N, pow_mul, mul_pow, h1, mul_pow, hP, ← zpow_natCast ((cg ^ N) ^ (-m)) 2,
        ← zpow_mul, mul_assoc, ← zpow_add]
      congr 2
      push_cast
      omega
    rw [pow_mul, hx, hq, pow_mul, hk1, one_pow]
