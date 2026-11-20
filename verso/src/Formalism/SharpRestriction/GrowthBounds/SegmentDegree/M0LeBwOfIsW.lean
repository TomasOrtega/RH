import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscPowerMonomialDegreeAtW

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section CD

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

/- English proof (translation)
Establish `hV` using `hX.valid`. Establish `h41` using `(top_count_lower_bounds 1088 (by norm_num) p n' r K X hX hLa hk).1`. Establish `hlt : x < X.F.fr j 0`. Establish `h1 : x ≤ X.F.fr (j - 1) (r - 1)` using `hW`. Establish `h2` using `TE.fr_prev_lt hV j`.

Use linear arithmetic over natural numbers and integers. Establish `hB` using `(TE.Bdeg_bounds hX hk h41 j b hA x hx hlt).1`. Establish `hc` using `(TE.c_bounds hX h41 j x hx).1`. Establish `B` using `basics hX`. Establish `hp0 : (0 : ℝ) < p` using `by linarith [B.p1]`.

Establish `hP : (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j)` using `by positivity`. Establish `hc' : (36 / 5 : ℝ) * X.Y * Dat.k (r` using `r) K ^ 2 * (X.Ns : ℝ) ≤ (X.a' p K (posOf n' x) : ℝ) / (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by`. Rewrite using `[le_div_iff₀ hP]`. Conclude with `hc`. Establish `hk5` using `B.k5`.

Establish `hN1` using `B.Ns1`. Establish `hY1` using `B.Y1`. Establish `hkN : 0 < Dat.k (r` using `r) K * (X.Ns : ℝ) := by nlinarith`. Establish `hbig : 2 * Dat.k (r` using `r) K * (X.Ns : ℝ) < (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by`. Establish `h1 : (36 / 5 : ℝ) * Dat.k (r` using `r) K ^ 2 * (X.Ns : ℝ) ≤ (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by`.

Establish `: 0 ≤ (36 / 5 : ℝ) * Dat.k (r` using `r) K ^ 2 * (X.Ns : ℝ) := by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2 : 2 * Dat.k (r` using `r) K * (X.Ns : ℝ) < (36 / 5 : ℝ) * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hpos : (0 : ℝ) < (X.Bdeg p K j (X.restr j b) x : ℝ)` using `by linarith`. Establish `hpos' : 0 < X.Bdeg p K j (X.restr j b) x` using `by exact_mod_cast hpos`. Unfold `Dat.Bdeg at hpos'`. Rewrite `hpos'` using `[if_pos hW]`. Use linear arithmetic over natural numbers and integers.
-/
theorem m0_le_Bw_of_isW (hX : X.Hyp p K) (hLa : 1088 ≤ X.CLa) (hk : 1088 ≤ X.Ck) (j : ℤ) (b : ℤ → ℕ)
    (hA : X.AdmLL p K j b) (x : ℤ) (hx : x ∈ X.F.letters j) (hW : X.F.IsW j x) : (X.m0 K : ℤ) ≤ X.Bw p K j x := by
  classical
  have hV := hX.valid
  have h41 := (top_count_lower_bounds 1088 (by norm_num) p n' r K X hX hLa hk).1
  have hlt : x < X.F.fr j 0 := by
    have h1 : x ≤ X.F.fr (j - 1) (r - 1) := hW
    have h2 := TE.fr_prev_lt hV j
    omega
  have hB := (TE.Bdeg_bounds hX hk h41 j b hA x hx hlt).1
  have hc := (TE.c_bounds hX h41 j x hx).1
  have B := basics hX
  have hp0 : (0 : ℝ) < p := by linarith [B.p1]
  have hP : (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by positivity
  have hc' : (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) ≤
      (X.a' p K (posOf n' x) : ℝ) / (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
    rw [le_div_iff₀ hP]; exact hc
  have hk5 := B.k5
  have hN1 := B.Ns1
  have hY1 := B.Y1
  have hkN : 0 < Dat.k (r := r) K * (X.Ns : ℝ) := by nlinarith
  have hbig : 2 * Dat.k (r := r) K * (X.Ns : ℝ) < (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    have h1 : (36 / 5 : ℝ) * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) ≤
        (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
      have : 0 ≤ (36 / 5 : ℝ) * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by positivity
      nlinarith
    have h2 : 2 * Dat.k (r := r) K * (X.Ns : ℝ) < (36 / 5 : ℝ) * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
      nlinarith
    linarith
  have hpos : (0 : ℝ) < (X.Bdeg p K j (X.restr j b) x : ℝ) := by linarith
  have hpos' : 0 < X.Bdeg p K j (X.restr j b) x := by exact_mod_cast hpos
  unfold Dat.Bdeg at hpos'
  rw [if_pos hW] at hpos'
  omega

/- English proof (translation)
Distinguish the cases in `hx : x ∈ X.F.letters j`. Take `⟨i, rfl⟩` from `segE_surj X.F j hx`. Rewrite using `[(segE_strictMono X.F j).injective.extend_apply]`. Conclude with `degAt_segRen X.F j hA i`. Rewrite using `[Function.extend_apply' _ _ _ (by`.

Introduce and unpack `⟨i, rfl⟩`. Conclude with `hx (segE_mem X.F j i))]`. Conclude with `mem_degAt_segRen_off j A x hx`.
-/
theorem mem_degAt_ext {R : Type} [CommRing R] (j : ℤ) {n : ℕ} {bb : Fin (segN X.F j) → ℕ}
    {A : MvPolynomial (Fin (segN X.F j) × Fin n) R} (hA : A ∈ Pol R n bb) (x : ℤ) :
    DegAt x (Function.extend (segE X.F j) bb 0 x) (segRen X.F j R n A) := by
  by_cases hx : x ∈ X.F.letters j
  · obtain ⟨i, rfl⟩ := segE_surj X.F j hx
    rw [(segE_strictMono X.F j).injective.extend_apply]
    exact degAt_segRen X.F j hA i
  · rw [Function.extend_apply' _ _ _ (by
      rintro ⟨i, rfl⟩
      exact hx (segE_mem X.F j i))]
    exact mem_degAt_segRen_off j A x hx

/- English proof (translation)
Unfold `Dat.restr`. Rewrite using `[if_pos hx]`.
-/
theorem mem_restr_late (j : ℤ) (b : ℤ → ℕ) (x : ℤ) (hx : x ∈ X.toLate j) : X.restr j b x = b x := by
  classical
  unfold Dat.restr
  rw [if_pos hx]

end CD

/- English proof (translation)
Introduce `p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q`. Establish `: Fact p.Prime` using `⟨hX.prime⟩`. Establish `hV` using `hX.valid`. Establish `hr : 0 < r` using `NeZero.pos r`. Establish `hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D` using `hAdm.2.2.2.2.2.2.2.2.1`.

Take `⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩` from `exists_path_decomposition D hAdm hX j b q`. Establish `H` using `plHyp_of X p K hX j _ _ dd hPATH`. Establish `hI' : IsSt P1.mu (Ican P1.mu)` using `by rw [h1]; exact mem_isSt_Ican H`. Establish `hI'' : IsSt P2.mu q.1.2.1` using `by rw [h2]; exact hSt`. Establish `u1` using `(standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI').1`.

Establish `u2` using `(standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI'').1`. Rewrite `u1` using `[h1]`. Rewrite `u2` using `[h2]`. Establish `hA : X.memA p K O j b q.1 ∈ Pol O r (fun x => X.discPowerMonomialDegree p K j b x + X.memdMu j q.1.2.2 x + Function.extend (segE X.F j) b' 0 x)` using `mem_Pol_of_degAt fun x => degAt_mul (degAt_mul (degAt_disc_power_monomial O j b x) (mem_degAt_Mu O j _ x)) (mem_degAt_ext j u1 x)`. Establish `hG : X.memG K O j q.1 ∈ Pol O K (Function.extend (segE X.F j) b'' 0)` using `mem_Pol_of_degAt fun x => mem_degAt_ext j u2 x`.

Establish `hprod` using `hom_Pol_mul O (plEmb_Pol r K hA) (nmEmb_Pol r K hG)`. Establish `hprev` using `TE.fr_prev_lt hV j`. Establish `heq : ((fun x => X.discPowerMonomialDegree p K j b x + X.memdMu j q.1.2.2 x + Function.extend (segE X.F j) b' 0 x) + Function.extend (segE X.F j) b'' 0) = b`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply]`.

Distinguish the cases in `hx : x ∈ X.F.letters j`. Take `⟨i, rfl⟩` from `segE_surj X.F j hx`. Rewrite using `[(segE_strictMono X.F j).injective.extend_apply, (segE_strictMono X.F j).injective.extend_apply]`. Establish `hs` using `hsum i`. Establish `hrN` using `k_r_le_segN X.F hV hr j`.

Establish `hil` using `i.isLt`. Distinguish the cases in `hi1 : i.val < r`. Establish `hxW` using `TE.dict_wE hV i hi1`. Establish `hW : X.F.IsW j (segE X.F j i)` using `(TE.dict_w hV i).mpr hi1`. Establish `hle : segE X.F j i ≤ X.F.fr (j - 1) (r - 1)` using `hW`.

Establish `hlt : segE X.F j i < X.F.fr j 0` using `by omega`. Establish `hdd` using `hPATH.degs i hlt`. Unfold `Dat.Bdeg at hdd`. Rewrite `hdd` using `[if_pos hW]`. Establish `hm0` using `m0_le_Bw_of_isW hX hLa hk j b hb.2.2 _ hx hW`.

Establish `hBw` using `hb.2.1 _ hx hW`. Establish `e1 : X.discPowerMonomialDegree p K j b (segE X.F j i) = X.m0 K + ((b (segE X.F j i) : ℤ) - X.Bw p K j (segE X.F j i)).toNat`. Use `disc_power_monomial_degree_at_w hX j b (⟨i.val, hi1⟩ : Fin r)` as an intermediate fact. Simplify using `only [] at this`. Rewrite `this` using `[← hxW]`.

Conclude with `this`. Establish `e2 : X.memdMu j q.1.2.2 (segE X.F j i) = 0` using `mem_dMu_off j _ _ fun a => by`. Use `kfr_le X.F hV j (Nat.zero_le a.val) a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[e1, e2]`.

Use linear arithmetic over natural numbers and integers. Establish `hnW : ¬ X.F.IsW j (segE X.F j i)` using `fun h => hi1 ((TE.dict_w hV i).mp h)`. Establish `hgt : X.F.fr (j - 1) (r - 1) < segE X.F j i` using `not_le.mp hnW`. Establish `hlate : segE X.F j i ∈ X.toLate j` using `(mem_late X j _).mpr ⟨hx, hnW⟩`. Establish `e1 : X.discPowerMonomialDegree p K j b (segE X.F j i) = 0` using `disc_power_monomial_degree_off j b _ fun a => by`.

Use `kfr_le X.F hV (j - 1) (by have := a.isLt; omega : a.val ≤ r - 1) (by omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `hi2 : i.val < segN X.F j - r`. Establish `hlt` using `(segE_lt_fr_iff X.F hV hr j i).mpr hi2`. Establish `hdd` using `hPATH.degs i hlt`.

Unfold `Dat.Bdeg at hdd`. Rewrite `hdd` using `[if_neg hnW, mem_restr_late j b _ hlate]`. Establish `e2 : X.memdMu j q.1.2.2 (segE X.F j i) = 0` using `mem_dMu_off j _ _ fun a => by`. Use `kfr_le X.F hV j (Nat.zero_le a.val) a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e1, e2]`. Use linear arithmetic over natural numbers and integers. Establish `ht : i.val - (segN X.F j - r) < r` using `by omega`. Establish `hseg : segE X.F j i = X.F.fr j (i.val - (segN X.F j - r))` using `(segE_eq_fr_iff X.F hV j i ht).mpr (by omega)`. Establish `hdi` using `hd i ⟨i.val - (segN X.F j - r), ht⟩ hseg`.

Establish `e2` using `mem_dMu_tau hX j q.1.2.2 (⟨i.val - (segN X.F j - r), ht⟩ : Fin r)`. Simplify using `only [] at e2 hdi`. Rewrite `e2`, `hdi` using `[← hseg]`. Rewrite `hdi` using `[mem_restr_late j b _ hlate]`. Rewrite using `[e1, e2]`.

Use linear arithmetic over natural numbers and integers. Establish `hne : ¬ ∃ a, segE X.F j a = x`. Introduce and unpack `⟨i, rfl⟩`. Conclude with `hx (segE_mem X.F j i)`. Rewrite using `[Function.extend_apply' _ _ _ hne, Function.extend_apply' _ _ _ hne, hb.1 x hx, disc_power_monomial_degree_off j b x fun a h => hx (h ▸ TE.frp_mem hV j a.val a.isLt), mem_dMu_off j _ x fun a h => hx (h ▸ k_fr_mem_letters X.F hV j a.isLt)]`.

Both sides reduce to the same expression. Rewrite `hprod` using `[heq]`. Conclude with `hprod`.
-/
theorem restMemC_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestMemC 1088 := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have H := plHyp_of X p K hX j _ _ dd hPATH
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := (standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI').1
  have u2 := (standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI'').1
  rw [h1] at u1
  rw [h2] at u2
  have hA : X.memA p K O j b q.1 ∈ Pol O r (fun x => X.discPowerMonomialDegree p K j b x + X.memdMu j q.1.2.2 x +
      Function.extend (segE X.F j) b' 0 x) :=
    mem_Pol_of_degAt fun x => degAt_mul (degAt_mul (degAt_disc_power_monomial O j b x) (mem_degAt_Mu O j _ x))
      (mem_degAt_ext j u1 x)
  have hG : X.memG K O j q.1 ∈ Pol O K (Function.extend (segE X.F j) b'' 0) :=
    mem_Pol_of_degAt fun x => mem_degAt_ext j u2 x
  have hprod := hom_Pol_mul O (plEmb_Pol r K hA) (nmEmb_Pol r K hG)
  have hprev := TE.fr_prev_lt hV j
  have heq : ((fun x => X.discPowerMonomialDegree p K j b x + X.memdMu j q.1.2.2 x + Function.extend (segE X.F j) b' 0 x) +
      Function.extend (segE X.F j) b'' 0) = b := by
    funext x
    simp only [Pi.add_apply]
    by_cases hx : x ∈ X.F.letters j
    · obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      rw [(segE_strictMono X.F j).injective.extend_apply, (segE_strictMono X.F j).injective.extend_apply]
      have hs := hsum i
      have hrN := k_r_le_segN X.F hV hr j
      have hil := i.isLt
      by_cases hi1 : i.val < r
      ·
        have hxW := TE.dict_wE hV i hi1
        have hW : X.F.IsW j (segE X.F j i) := (TE.dict_w hV i).mpr hi1
        have hle : segE X.F j i ≤ X.F.fr (j - 1) (r - 1) := hW
        have hlt : segE X.F j i < X.F.fr j 0 := by omega
        have hdd := hPATH.degs i hlt
        unfold Dat.Bdeg at hdd
        rw [if_pos hW] at hdd
        have hm0 := m0_le_Bw_of_isW hX hLa hk j b hb.2.2 _ hx hW
        have hBw := hb.2.1 _ hx hW
        have e1 : X.discPowerMonomialDegree p K j b (segE X.F j i) = X.m0 K +
            ((b (segE X.F j i) : ℤ) - X.Bw p K j (segE X.F j i)).toNat := by
          have := disc_power_monomial_degree_at_w hX j b (⟨i.val, hi1⟩ : Fin r)
          simp only [] at this
          rw [← hxW] at this
          exact this
        have e2 : X.memdMu j q.1.2.2 (segE X.F j i) = 0 := mem_dMu_off j _ _ fun a => by
          have := kfr_le X.F hV j (Nat.zero_le a.val) a.isLt
          omega
        rw [e1, e2]
        omega
      · have hnW : ¬ X.F.IsW j (segE X.F j i) := fun h => hi1 ((TE.dict_w hV i).mp h)
        have hgt : X.F.fr (j - 1) (r - 1) < segE X.F j i := not_le.mp hnW
        have hlate : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hnW⟩
        have e1 : X.discPowerMonomialDegree p K j b (segE X.F j i) = 0 := disc_power_monomial_degree_off j b _ fun a => by
          have := kfr_le X.F hV (j - 1) (by have := a.isLt; omega : a.val ≤ r - 1) (by omega)
          omega
        by_cases hi2 : i.val < segN X.F j - r
        · have hlt := (segE_lt_fr_iff X.F hV hr j i).mpr hi2
          have hdd := hPATH.degs i hlt
          unfold Dat.Bdeg at hdd
          rw [if_neg hnW, mem_restr_late j b _ hlate] at hdd
          have e2 : X.memdMu j q.1.2.2 (segE X.F j i) = 0 := mem_dMu_off j _ _ fun a => by
            have := kfr_le X.F hV j (Nat.zero_le a.val) a.isLt
            omega
          rw [e1, e2]
          omega
        · have ht : i.val - (segN X.F j - r) < r := by omega
          have hseg : segE X.F j i = X.F.fr j (i.val - (segN X.F j - r)) :=
            (segE_eq_fr_iff X.F hV j i ht).mpr (by omega)
          have hdi := hd i ⟨i.val - (segN X.F j - r), ht⟩ hseg
          have e2 := mem_dMu_tau hX j q.1.2.2 (⟨i.val - (segN X.F j - r), ht⟩ : Fin r)
          simp only [] at e2 hdi
          rw [← hseg] at e2 hdi
          rw [mem_restr_late j b _ hlate] at hdi
          rw [e1, e2]
          omega
    · have hne : ¬ ∃ a, segE X.F j a = x := by
        rintro ⟨i, rfl⟩
        exact hx (segE_mem X.F j i)
      rw [Function.extend_apply' _ _ _ hne, Function.extend_apply' _ _ _ hne, hb.1 x hx,
        disc_power_monomial_degree_off j b x fun a h => hx (h ▸ TE.frp_mem hV j a.val a.isLt),
        mem_dMu_off j _ x fun a h => hx (h ▸ k_fr_mem_letters X.F hV j a.isLt)]
      rfl
  rw [heq] at hprod
  exact hprod

/- English proof (translation)
Introduce `p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q`. Establish `: Fact p.Prime` using `⟨hX.prime⟩`. Establish `hV` using `hX.valid`. Establish `hr : 0 < r` using `NeZero.pos r`. Establish `hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D` using `hAdm.2.2.2.2.2.2.2.2.1`.

Take `⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩` from `exists_path_decomposition D hAdm hX j b q`. Establish `H` using `plHyp_of X p K hX j _ _ dd hPATH`. Establish `hI' : IsSt P1.mu (Ican P1.mu)` using `by rw [h1]; exact mem_isSt_Ican H`. Establish `hI'' : IsSt P2.mu q.1.2.1` using `by rw [h2]; exact hSt`. Establish `u1` using `(standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI').1`.

Establish `u2` using `(standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI'').1`. Rewrite `u1` using `[h1]`. Rewrite `u2` using `[h2]`. Establish `hA : X.discPowerTimesMonomial p K O j b * X.memPl K O j q.1.1 ∈ Pol O r (fun x => X.discPowerMonomialDegree p K j b x + Function.extend (segE X.F j) b' 0 x)` using `mem_Pol_of_degAt fun x => degAt_mul (degAt_disc_power_monomial O j b x) (mem_degAt_ext j u1 x)`. Establish `hG : X.memG K O j q.1 ∈ Pol O K (Function.extend (segE X.F j) b'' 0)` using `mem_Pol_of_degAt fun x => mem_degAt_ext j u2 x`.

Establish `hprod` using `hom_Pol_mul O (plEmb_Pol r K hA) (nmEmb_Pol r K hG)`. Establish `hMu : plEmb O r K (X.memMu O j q.1.2.2) = monomial (X.monTau K j q.1.2.2) (1 : O)`. Unfold `Dat.memMu Dat.monTau`. Rewrite using `[MvPolynomial.monomial_sum_one, map_prod]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[map_pow, ← MvPolynomial.X_pow_eq_monomial]`. Simplify using `[plEmb]`. Establish `hfac : plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) = monomial (X.monTau K j q.1.2.2) (1 : O) * (plEmb O r K (X.discPowerTimesMonomial p K O j b * X.memPl K O j q.1.1) * nmEmb O r K (X.memG K O j q.1))`. Rewrite using `[← hMu]`. Unfold `Dat.memA`.

Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfac, MvPolynomial.mem_restrictSupport_iff]`. Introduce `mm hmm i hi c`. Establish `hmm' : coeff mm (monomial (X.monTau K j q.1.2.2) (1 : O) * (plEmb O r K (X.discPowerTimesMonomial p K O j b * X.memPl K O j q.1.1) * nmEmb O r K (X.memG K O j q.1))) ≠ 0`.

Rewrite using `[← MvPolynomial.mem_support_iff]`. Conclude with `hmm` after adjusting the coercions. Rewrite `hmm'` using `[MvPolynomial.coeff_monomial_mul']`. Use `split_ifs at hmm' with hle`. Rewrite `hmm'` using `[one_mul]`.

Establish `hsupp` using `MvPolynomial.mem_support_iff.mpr hmm'`. Establish `hdeg` using `mem_Pol_iff.mp hprod _ hsupp (X.F.fr j i)`. Establish `hrN` using `k_r_le_segN X.F hV hr j`. Set `idx : Fin (segN X.F j)` to `⟨segN X.F j - r + i, by omega⟩`. Establish `hidx : segE X.F j idx = X.F.fr j i` using `(segE_eq_fr_iff X.F hV j idx hi).mpr rfl`.

Establish `hprev` using `TE.fr_prev_lt hV j`. Establish `e1 : X.discPowerMonomialDegree p K j b (X.F.fr j i) = 0` using `disc_power_monomial_degree_off j b _ fun a => by`. Establish `h3` using `kfr_le X.F hV (j - 1) (by have := a.isLt; omega : a.val ≤ r - 1) (by omega)`. Establish `h4` using `kfr_le X.F hV j (Nat.zero_le i) hi`. Use linear arithmetic over natural numbers and integers.

Simplify using `only [Pi.add_apply] at hdeg`. Rewrite `hdeg` using `[e1, ← hidx, (segE_strictMono X.F j).injective.extend_apply, (segE_strictMono X.F j).injective.extend_apply, hidx]`. Establish `h21` using `tau_degree_on_path_bound p n' r K X hX j _ _ dd hPATH idx (by`. Rewrite using `[hidx]`. Conclude with `kfr_le X.F hV j (Nat.zero_le i) hi)`.

Establish `hs` using `hsum idx`. Establish `hone : (mm - X.monTau K j q.1.2.2) (X.F.fr j i, Fin.castAdd K c) ≤ multideg (mm - X.monTau K j q.1.2.2) (X.F.fr j i)`. Unfold `multideg`. Conclude with `Finset.single_le_sum (f := fun c' => (mm - X.monTau K j q.1.2.2) (X.F.fr j i, c')) (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Fin.castAdd K c))`. Establish `hdec : mm (X.F.fr j i, Fin.castAdd K c) = X.monTau K j q.1.2.2 (X.F.fr j i, Fin.castAdd K c) + (mm - X.monTau K j q.1.2.2) (X.F.fr j i, Fin.castAdd K c)`.

Use `congrArg (fun f => f (X.F.fr j i, Fin.castAdd K c)) (add_tsub_cancel_of_le hle)` as an intermediate fact. Simplify using `only [Finsupp.add_apply] at this`. Conclude with `this.symm`. Establish `hmt` using `monTau_apply X K hV j q.1.2.2 (⟨i, hi⟩ : Fin r) c`. Simplify using `only [] at hmt`.

Establish `huv` using `hu (⟨i, hi⟩, c)`. Rewrite using `[hdec, hmt]`. Use linear arithmetic over natural numbers and integers. Conclude with `absurd rfl hmm'`.
-/
theorem restMemD_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestMemD C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have H := plHyp_of X p K hX j _ _ dd hPATH
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := (standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI').1
  have u2 := (standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI'').1
  rw [h1] at u1
  rw [h2] at u2
  have hA : X.discPowerTimesMonomial p K O j b * X.memPl K O j q.1.1 ∈ Pol O r (fun x => X.discPowerMonomialDegree p K j b x +
      Function.extend (segE X.F j) b' 0 x) :=
    mem_Pol_of_degAt fun x => degAt_mul (degAt_disc_power_monomial O j b x) (mem_degAt_ext j u1 x)
  have hG : X.memG K O j q.1 ∈ Pol O K (Function.extend (segE X.F j) b'' 0) :=
    mem_Pol_of_degAt fun x => mem_degAt_ext j u2 x
  have hprod := hom_Pol_mul O (plEmb_Pol r K hA) (nmEmb_Pol r K hG)
  have hMu : plEmb O r K (X.memMu O j q.1.2.2) = monomial (X.monTau K j q.1.2.2) (1 : O) := by
    unfold Dat.memMu Dat.monTau
    rw [MvPolynomial.monomial_sum_one, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_pow, ← MvPolynomial.X_pow_eq_monomial]
    simp [plEmb]
  have hfac : plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) =
      monomial (X.monTau K j q.1.2.2) (1 : O) *
        (plEmb O r K (X.discPowerTimesMonomial p K O j b * X.memPl K O j q.1.1) * nmEmb O r K (X.memG K O j q.1)) := by
    rw [← hMu]
    unfold Dat.memA
    simp only [map_mul]
    ring
  rw [hfac, MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm i hi c
  have hmm' : coeff mm (monomial (X.monTau K j q.1.2.2) (1 : O) *
      (plEmb O r K (X.discPowerTimesMonomial p K O j b * X.memPl K O j q.1.1) * nmEmb O r K (X.memG K O j q.1))) ≠ 0 := by
    rw [← MvPolynomial.mem_support_iff]; exact_mod_cast hmm
  rw [MvPolynomial.coeff_monomial_mul'] at hmm'
  split_ifs at hmm' with hle
  · rw [one_mul] at hmm'
    have hsupp := MvPolynomial.mem_support_iff.mpr hmm'
    have hdeg := mem_Pol_iff.mp hprod _ hsupp (X.F.fr j i)
    have hrN := k_r_le_segN X.F hV hr j
    let idx : Fin (segN X.F j) := ⟨segN X.F j - r + i, by omega⟩
    have hidx : segE X.F j idx = X.F.fr j i := (segE_eq_fr_iff X.F hV j idx hi).mpr rfl
    have hprev := TE.fr_prev_lt hV j
    have e1 : X.discPowerMonomialDegree p K j b (X.F.fr j i) = 0 := disc_power_monomial_degree_off j b _ fun a => by
      have h3 := kfr_le X.F hV (j - 1) (by have := a.isLt; omega : a.val ≤ r - 1) (by omega)
      have h4 := kfr_le X.F hV j (Nat.zero_le i) hi
      omega
    simp only [Pi.add_apply] at hdeg
    rw [e1, ← hidx, (segE_strictMono X.F j).injective.extend_apply,
      (segE_strictMono X.F j).injective.extend_apply, hidx] at hdeg
    have h21 := tau_degree_on_path_bound p n' r K X hX j _ _ dd hPATH idx (by
      rw [hidx]; exact kfr_le X.F hV j (Nat.zero_le i) hi)
    have hs := hsum idx
    have hone : (mm - X.monTau K j q.1.2.2) (X.F.fr j i, Fin.castAdd K c) ≤
        multideg (mm - X.monTau K j q.1.2.2) (X.F.fr j i) := by
      unfold multideg
      exact Finset.single_le_sum (f := fun c' => (mm - X.monTau K j q.1.2.2) (X.F.fr j i, c'))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (Fin.castAdd K c))
    have hdec : mm (X.F.fr j i, Fin.castAdd K c) = X.monTau K j q.1.2.2 (X.F.fr j i, Fin.castAdd K c) +
        (mm - X.monTau K j q.1.2.2) (X.F.fr j i, Fin.castAdd K c) := by
      have := congrArg (fun f => f (X.F.fr j i, Fin.castAdd K c)) (add_tsub_cancel_of_le hle)
      simp only [Finsupp.add_apply] at this
      exact this.symm
    have hmt := monTau_apply X K hV j q.1.2.2 (⟨i, hi⟩ : Fin r) c
    simp only [] at hmt
    have huv := hu (⟨i, hi⟩, c)
    rw [hdec, hmt]
    omega
  · exact absurd rfl hmm'

/- English proof (translation)
The claim follows from `restMem_of_rests 1088 (restMemA_of D hAdm 1088) (restMemB_of D hAdm 1088) (restMemC_of D hAdm) (restMemD_of D hAdm 1088)`.
-/
theorem restMem_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : RestMem 1088 :=
  restMem_of_rests 1088 (restMemA_of D hAdm 1088) (restMemB_of D hAdm 1088) (restMemC_of D hAdm)
    (restMemD_of D hAdm 1088)

end Formalism.MainNotions.SelectionLemmas.Pf
