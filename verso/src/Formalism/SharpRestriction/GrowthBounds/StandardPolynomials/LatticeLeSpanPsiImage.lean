import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColGen

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.PolBridge

section Span

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

/- English proof (translation)
Establish `hp : p.Prime` using `Fact.out`. Establish `hKz : CharZero (KK O)` using `dvr_fraction_field_charZero S hp`. Establish `hinj : Function.Injective (algebraMap O (KK O))` using `IsFractionRing.injective O (KK O)`. Take `⟨hli, hspan⟩` from `hA2 O N r (⟨LL.vec⟩ : Letters (Fin N)) LL.deg`. Establish `hli' : LinearIndependent O (psiR (r` using `r) O LL) := hli`.

Establish `hrange : Submodule.span O (Set.range (psiR (r` using `r) O LL)) = Pol O r LL.deg := by`. Rewrite using `[← hspan]`. Use `congr 1`. Use extensionality with `G`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x.1.1, x.1.2, x.2, rfl⟩`. Introduce and unpack `⟨P, I, h, rfl⟩`. Conclude with `⟨⟨(P, I), h⟩, rfl⟩`. Establish `hfin : Finite (Tx r LL)` using `tx_finite LL hli' hrange`.

Take `⟨Bd, hBd⟩` from `exists_bound (r := r) (Lt := (⟨LL.vec⟩ : Letters (Fin N))) (B := LL.deg)`. Establish `hC1` using `one_cond D LL hrange hspan (fun th M => (hA3 p O S N r _ LL.deg th M).1) Bd hBd J M hJ`. Introduce `F hF`. Take `⟨hY, G, hG⟩` from `hF`. Set `φ : MvPolynomial (Fin N × Fin r) O →ₗ[O] MvPolynomial (Fin N × Fin r) (KK O)` to `(MvPolynomial.mapAlgHom (Algebra.ofId O (KK O))).toLinearMap`.

Establish `hG' : MvPolynomial.map (algebraMap O (KK O)) G = F` using `hG`. Establish `hY' : MvPolynomial.map (algebraMap O (KK O)) G ∈ Yjt (KK O) (r` using `r) LL J M := by rw [hG']; exact hY`. Rewrite `hY'` using `[Yjt, Submodule.mem_inf, Submodule.mem_iInf]`. Establish `hGP : G ∈ Pol O r LL.deg` using `(map_mem_Pol_iff _ hinj _ G).1 hY'.1`. Establish `hGs : G ∈ Submodule.span O (psiR O LL '' sAll LL J M)` using `mem_span_iInter hli' (sK LL J M) (hrange ▸ hGP) (fun k => (hC1 k G hGP).1 (hY'.2 k))`.

Establish `h1 : F ∈ Submodule.map φ (Submodule.span O (psiR O LL '' sAll LL J M))` using `⟨G, hGs, hG⟩`. Rewrite `h1` using `[Submodule.map_span, ← Set.image_comp]`. Establish `h2 : (φ ∘ psiR (r` using `r) O LL) = psiR (KK O) LL := funext fun x => psiR_map LL x`. Rewrite `h1` using `[h2]`. Then use the resulting hypothesis.
-/
theorem lattice_le_span_psi_image {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (hJ : ∀ k, J k ≤ N) :
    YjtZ O (r := r) LL J M ≤ Submodule.span O (psiR (KK O) LL '' sAll LL J M) := by
  have hp : p.Prime := Fact.out
  have hKz : CharZero (KK O) := dvr_fraction_field_charZero S hp
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  obtain ⟨hli, hspan⟩ := hA2 O N r (⟨LL.vec⟩ : Letters (Fin N)) LL.deg
  have hli' : LinearIndependent O (psiR (r := r) O LL) := hli
  have hrange : Submodule.span O (Set.range (psiR (r := r) O LL)) = Pol O r LL.deg := by
    rw [← hspan]
    congr 1
    ext G
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.1.1, x.1.2, x.2, rfl⟩
    · rintro ⟨P, I, h, rfl⟩; exact ⟨⟨(P, I), h⟩, rfl⟩
  have hfin : Finite (Tx r LL) := tx_finite LL hli' hrange
  obtain ⟨Bd, hBd⟩ := exists_bound (r := r) (Lt := (⟨LL.vec⟩ : Letters (Fin N))) (B := LL.deg)
  have hC1 := one_cond D LL hrange hspan (fun th M => (hA3 p O S N r _ LL.deg th M).1) Bd hBd J M hJ
  intro F hF
  obtain ⟨hY, G, hG⟩ := hF
  let φ : MvPolynomial (Fin N × Fin r) O →ₗ[O] MvPolynomial (Fin N × Fin r) (KK O) :=
    (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O))).toLinearMap
  have hG' : MvPolynomial.map (algebraMap O (KK O)) G = F := hG
  have hY' : MvPolynomial.map (algebraMap O (KK O)) G ∈ Yjt (KK O) (r := r) LL J M := by rw [hG']; exact hY
  rw [Yjt, Submodule.mem_inf, Submodule.mem_iInf] at hY'
  have hGP : G ∈ Pol O r LL.deg := (map_mem_Pol_iff _ hinj _ G).1 hY'.1
  have hGs : G ∈ Submodule.span O (psiR O LL '' sAll LL J M) :=
    mem_span_iInter hli' (sK LL J M) (hrange ▸ hGP) (fun k => (hC1 k G hGP).1 (hY'.2 k))
  have h1 : F ∈ Submodule.map φ (Submodule.span O (psiR O LL '' sAll LL J M)) := ⟨G, hGs, hG⟩
  rw [Submodule.map_span, ← Set.image_comp] at h1
  have h2 : (φ ∘ psiR (r := r) O LL) = psiR (KK O) LL := funext fun x => psiR_map LL x
  rwa [h2] at h1

end Span

section Xi

variable {O : Type} [CommRing O] [IsDomain O]

/- English proof (translation)
Introduce `c d h`. Simplify `h` using `[xiVar]`.
-/
theorem xiVar_inj (N r t : ℕ) : Function.Injective (xiVar N r t) := by
  intro c d h
  simpa [xiVar] using h

/- English proof (translation)
Introduce `f hf`. Take `⟨h1, h2⟩` from `Submodule.mem_inf.1 hf`. Take `⟨g, rfl⟩` from `LinearMap.mem_range.1 h2`. Establish `hinj : Function.Injective (algebraMap O (KK O))` using `IsFractionRing.injective O (KK O)`. Establish `hmap : ∀ p : MvPolynomial (BVar N r t) O, (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial (BVar N r t) O →ₐ[O] _).toLinearMap p = MvPolynomial.map (algebraMap O (KK O)) p` using `fun p => rfl`.

Establish `hsup : ∀ m ∈ g.support, (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b`. Introduce `m hm`. Establish `hm' : m ∈ (MvPolynomial.map (algebraMap O (KK O)) g).support`. Rewrite using `[MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]`. Conclude with `(map_ne_zero_iff _ hinj).2 (MvPolynomial.mem_support_iff.1 hm)`.

Rewrite `h1` using `[hmap]`. Conclude with `((MvPolynomial.mem_restrictSupport_iff (KK O)).1 h1) (Finset.mem_coe.2 hm')`. Rewrite using `[hmap, MvPolynomial.as_sum g, map_sum]`. Use `Submodule.sum_mem _ (fun m hm => ?_)` and prove the remaining obligations. Take `⟨hv, hb⟩` from `hsup m hm`.

Establish `hmon : m.prod (fun v e => (X v : MvPolynomial (BVar N r t) (KK O)) ^ e) = ∏ c, X (xiVar N r t c) ^ m (xiVar N r t c)`. Rewrite using `[Finsupp.prod, ← Finset.prod_image (fun c _ c' _ h => xiVar_inj N r t h) (f := fun v => (X v : MvPolynomial (BVar N r t) (KK O)) ^ m v)]`. Apply `Finset.prod_subset` to reduce the goal to its premises. Introduce `v hv'`. Take `⟨c, rfl⟩` from `hv v hv'`.

Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ c)`. Introduce `v _ hv'`. Establish `h0 : m v = 0` using `by simpa using hv'`. Rewrite using `[h0, pow_zero]`. Establish `hprod1 : m.prod (fun v e => (X v : MvPolynomial (BVar N r t) (KK O)) ^ e) = MvPolynomial.monomial m 1`.

Rewrite using `[MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]`. Establish `hterm : MvPolynomial.map (algebraMap O (KK O)) (MvPolynomial.monomial m (g.coeff m)) = g.coeff m • ∏ c, X (xiVar N r t c) ^ m (xiVar N r t c)`. Rewrite using `[← hmon, hprod1, MvPolynomial.smul_monomial, Algebra.smul_def, mul_one, MvPolynomial.map_monomial]`. Rewrite using `[hterm]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun c => m (xiVar N r t c), hb, rfl⟩)`.
-/
theorem xiSpan (N r t b : ℕ) :
    XiPolZ O N r t b ≤ Submodule.span O
      {g : MvPolynomial (BVar N r t) (KK O) | ∃ γ : Fin r → ℕ, ∑ c, γ c = b ∧ g = ∏ c, X (xiVar N r t c) ^ γ c} := by
  intro f hf
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hf
  obtain ⟨g, rfl⟩ := LinearMap.mem_range.1 h2
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (KK O)
  have hmap : ∀ p : MvPolynomial (BVar N r t) O,
      (MvPolynomial.mapAlgHom (Algebra.ofId O (KK O)) : MvPolynomial (BVar N r t) O →ₐ[O] _).toLinearMap p =
        MvPolynomial.map (algebraMap O (KK O)) p := fun p => rfl
  have hsup : ∀ m ∈ g.support, (∀ v ∈ m.support, ∃ c, v = xiVar N r t c) ∧ ∑ c, m (xiVar N r t c) = b := by
    intro m hm
    have hm' : m ∈ (MvPolynomial.map (algebraMap O (KK O)) g).support := by
      rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_map]
      exact (map_ne_zero_iff _ hinj).2 (MvPolynomial.mem_support_iff.1 hm)
    rw [hmap] at h1
    exact ((MvPolynomial.mem_restrictSupport_iff (KK O)).1 h1) (Finset.mem_coe.2 hm')
  rw [hmap, MvPolynomial.as_sum g, map_sum]
  refine Submodule.sum_mem _ (fun m hm => ?_)
  obtain ⟨hv, hb⟩ := hsup m hm
  have hmon : m.prod (fun v e => (X v : MvPolynomial (BVar N r t) (KK O)) ^ e) =
      ∏ c, X (xiVar N r t c) ^ m (xiVar N r t c) := by
    rw [Finsupp.prod, ← Finset.prod_image (fun c _ c' _ h => xiVar_inj N r t h)
      (f := fun v => (X v : MvPolynomial (BVar N r t) (KK O)) ^ m v)]
    apply Finset.prod_subset
    · intro v hv'
      obtain ⟨c, rfl⟩ := hv v hv'
      exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
    · intro v _ hv'
      have h0 : m v = 0 := by simpa using hv'
      rw [h0, pow_zero]
  have hprod1 : m.prod (fun v e => (X v : MvPolynomial (BVar N r t) (KK O)) ^ e) = MvPolynomial.monomial m 1 := by
    rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul]
  have hterm : MvPolynomial.map (algebraMap O (KK O)) (MvPolynomial.monomial m (g.coeff m)) =
      g.coeff m • ∏ c, X (xiVar N r t c) ^ m (xiVar N r t c) := by
    rw [← hmon, hprod1, MvPolynomial.smul_monomial, Algebra.smul_def, mul_one, MvPolynomial.map_monomial]
  rw [hterm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun c => m (xiVar N r t c), hb, rfl⟩)

end Xi

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r]

/- English proof (translation)
Introduce `x hx`. Simplify using `only [genSet, Set.mem_iUnion] at hx`. Take `⟨j, jp, hok, y, hy, g, hg, rfl⟩` from `hx`. Establish `key : ∀ y ∈ Submodule.span O (psiR (KK O) (B.lettersAt j jp) '' sAll (B.lettersAt j jp) B.T.J B.T.thr), ∀ g ∈ Submodule.span O {g : MvPolynomial (BVar N r B.T.t) (KK O) | ∃ γ : Fin r → ℕ, ∑ c, γ c = B.B - jp ∧ g = ∏ c, X (xiVar N r B.T.t c) ^ γ c}, ((∏ i, B.Ehat O (r` using `r) i ^ j i) * B.Eplus O (r := r) ^ jp * (∏ i, X (scalZ N r B.T.t (Fin.castSucc i)) ^ B.T.z i) * X (scalZ N r B.T.t (Fin.last B.T.t)) ^ B.zPlus) * rename (chainEmb N r B.T.t) y * g ∈ Submodule.span O (colGens O (r := r) B) := by`. Introduce `y hy g hg`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y0 hy0`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem g0 hg0`. Take `⟨yy, hyy, rfl⟩` from `hy0`.

Take `⟨γ, hγ, rfl⟩` from `hg0`. Conclude with `Submodule.subset_span ⟨j, jp, hok, yy, hyy, γ, hγ, rfl⟩`. Consider the case `zero => simp`. Consider the case `add g1 g2 _ _ h1 h2`. Rewrite using `[mul_add]`.

Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul a g1 _ h1`. Rewrite using `[mul_smul_comm]`. Conclude with `Submodule.smul_mem _ a h1`. Consider the case `zero => simp`.

Consider the case `add y1 y2 _ _ h1 h2`. Rewrite using `[map_add, mul_add, add_mul]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul a y1 _ h1`. Rewrite using `[AlgHom.map_smul_of_tower, mul_smul_comm, smul_mul_assoc]`.

Conclude with `Submodule.smul_mem _ a h1`. Conclude with `key y (lattice_le_span_psi_image (r := r) hA2 hA3 S (B.lettersAt j jp) B.T.J B.T.thr hJ hy) g (xiSpan (O := O) N r B.T.t (B.B - jp) hg)`.
-/
theorem genSet_le {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) {p : ℕ} [Fact p.Prime]
    (S : UniformizedDVR p O) (B : BlockData N) (hJ : ∀ k, B.T.J k ≤ N) :
    genSet O (r := r) B ⊆ Submodule.span O (colGens O (r := r) B) := by
  intro x hx
  simp only [genSet, Set.mem_iUnion] at hx
  obtain ⟨j, jp, hok, y, hy, g, hg, rfl⟩ := hx
  have key : ∀ y ∈ Submodule.span O (psiR (KK O) (B.lettersAt j jp) '' sAll (B.lettersAt j jp) B.T.J B.T.thr),
      ∀ g ∈ Submodule.span O {g : MvPolynomial (BVar N r B.T.t) (KK O) |
        ∃ γ : Fin r → ℕ, ∑ c, γ c = B.B - jp ∧ g = ∏ c, X (xiVar N r B.T.t c) ^ γ c},
      ((∏ i, B.Ehat O (r := r) i ^ j i) * B.Eplus O (r := r) ^ jp *
          (∏ i, X (scalZ N r B.T.t (Fin.castSucc i)) ^ B.T.z i) * X (scalZ N r B.T.t (Fin.last B.T.t)) ^ B.zPlus) * rename (chainEmb N r B.T.t) y * g ∈ Submodule.span O (colGens O (r := r) B) := by
    intro y hy g hg
    induction hy using Submodule.span_induction with
    | mem y0 hy0 =>
      induction hg using Submodule.span_induction with
      | mem g0 hg0 =>
        obtain ⟨yy, hyy, rfl⟩ := hy0
        obtain ⟨γ, hγ, rfl⟩ := hg0
        exact Submodule.subset_span ⟨j, jp, hok, yy, hyy, γ, hγ, rfl⟩
      | zero => simp
      | add g1 g2 _ _ h1 h2 =>
        rw [mul_add]
        exact Submodule.add_mem _ h1 h2
      | smul a g1 _ h1 =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ a h1
    | zero => simp
    | add y1 y2 _ _ h1 h2 =>
      rw [map_add, mul_add, add_mul]
      exact Submodule.add_mem _ h1 h2
    | smul a y1 _ h1 =>
      rw [AlgHom.map_smul_of_tower, mul_smul_comm, smul_mul_assoc]
      exact Submodule.smul_mem _ a h1
  exact key y (lattice_le_span_psi_image (r := r) hA2 hA3 S (B.lettersAt j jp) B.T.J B.T.thr hJ hy) g
    (xiSpan (O := O) N r B.T.t (B.B - jp) hg)

/- English proof (translation)
Use `show (if h : (k : ℕ) < S.t then 2 * (uTop S ⟨k, h⟩ : ℕ) + 1 else 2 * s + 1) ≤ 2 * s + 1`. Use `split_ifs with h`. Use `(uTop S ⟨k, h⟩).isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `le_rfl`.
-/
theorem blockData_J_le (p : ℕ) {s r : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (k : Fin (blockData p S aTop aPlus m b).T.q) : (blockData p S aTop aPlus m b).T.J k ≤ 2 * s + 1 := by
  show (if h : (k : ℕ) < S.t then 2 * (uTop S ⟨k, h⟩ : ℕ) + 1 else 2 * s + 1) ≤ 2 * s + 1
  split_ifs with h
  · have := (uTop S ⟨k, h⟩).isLt
    omega
  · exact le_rfl

end Gen

/- English proof (translation)
Introduce `_ _ X _ _ O _ _ _ _ S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s hs`. Establish `hmem : symFam (KK O) X.p C0 CE1 CE2 X β s ∈ liftSub C0 Cde CE1 CE2 X O S.w mm n (ordFam C0 CE1 CE2 X β)` using `symFam_span β (fun j => colGens O (r := X.m) (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j))) _ (fun s' hs' => (hF X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s' hs').some.liftable S.w_irr.ne_zero) s (fun j => genSet_ …`. Take `⟨raw, hc, τ, hτ, hw⟩` from `hmem`. Conclude with `⟨raw, τ, hc, hτ, hw⟩`.
-/
theorem asmRTAt_of_facSys {D : Formalism.BasicNotions.D7} (hA2 : Formalism.MainNotions.CovariantDegrees.HyperplaneRank D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D)
    {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hF : FacSysAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    AsmRTAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro _ _ X _ _ O _ _ _ _ S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s hs
  have hmem : symFam (KK O) X.p C0 CE1 CE2 X β s ∈
      liftSub C0 Cde CE1 CE2 X O S.w mm n (ordFam C0 CE1 CE2 X β) :=
    symFam_span β (fun j => colGens O (r := X.m)
        (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j))) _
      (fun s' hs' => (hF X O S hSq hD1 hHI hCB mm hmm n hn1 hnc β hβ s' hs').some.liftable S.w_irr.ne_zero) s
      (fun j => genSet_le hA2 hA3 S _ (blockData_J_le _ _ _ _ _ _) (hs j))
  obtain ⟨raw, hc, τ, hτ, hw⟩ := hmem
  exact ⟨raw, τ, hc, hτ, hw⟩

/- English proof (translation)
Unfold `admitted at hA`. Take `⟨-, -, -, -, -, h6, -, -, -, -, -, -, -, -, h15, -⟩` from `hA`. Introduce `Cc hCc`. Take `⟨T0, hT0, h1⟩` from `h Cc hCc`. Use `⟨T0, hT0, fun C0 hC0 => ?_⟩` and prove the remaining obligations.

Take `⟨T1, hT1, h2⟩` from `h1 C0 hC0`. Use `⟨T1, hT1, fun CE1 CE2 Cm hE1 hE2 hm => ?_⟩` and prove the remaining obligations. Take `⟨T2, hT2, h3⟩` from `h2 CE1 CE2 Cm hE1 hE2 hm`. Conclude with `⟨T2, hT2, fun CYb Cde Ck CD Cb a b c d e => asmRTAt_of_facSys (D := D) h15 h6 (h3 CYb Cde Ck CD Cb a b c d e)⟩`.
-/
theorem restAsmRT_of_facSys {D : Formalism.BasicNotions.D7} (hA : admitted D) (h : FacSysCondition) : RestAsmRT := by
  unfold admitted at hA
  obtain ⟨-, -, -, -, -, h6, -, -, -, -, -, -, -, -, h15, -⟩ := hA
  intro Cc hCc
  obtain ⟨T0, hT0, h1⟩ := h Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h2⟩ := h1 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 Cm hE1 hE2 hm => ?_⟩
  obtain ⟨T2, hT2, h3⟩ := h2 CE1 CE2 Cm hE1 hE2 hm
  exact ⟨T2, hT2, fun CYb Cde Ck CD Cb a b c d e =>
    asmRTAt_of_facSys (D := D) h15 h6 (h3 CYb Cde Ck CD Cb a b c d e)⟩

end Formalism.MainNotions.ColumnSystems.Pf
