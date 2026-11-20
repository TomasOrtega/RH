import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
import Formalism.GradedWeylDivisibility.FinalC

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

/- English proof (translation)
Introduce `i j hij`. Use `mu.anti hij` as an intermediate fact. Unfold `DomWeight.natW`. Conclude with `Int.toNat_le_toNat (by omega)`.
-/
theorem lm_natW_anti {k : ℕ} (mu : DomWeight k) : Antitone mu.natW := by
  intro i j hij
  have := mu.anti hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by omega)

/- English proof (translation)
Unfold `Formalism.REAL.fockF`. Apply `Finset.sum_subset hs` to reduce the goal to its premises. Introduce `m _ hm`. Rewrite using `[MvPolynomial.notMem_support_iff.mp hm]`. Simplify using the standard rewrite rules.
-/
theorem lm_fockF_eq_sum {σ : Type*} (f g : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    Formalism.REAL.fockF f g =
      ∑ m ∈ s, f.coeff m * star (g.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
  unfold Formalism.REAL.fockF
  apply Finset.sum_subset hs
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm]
  simp

/- English proof (translation)
Rewrite using `[lm_fockF_eq_sum (f1 + f2) g (f1.support ∪ f2.support) MvPolynomial.support_add, lm_fockF_eq_sum f1 g _ Finset.subset_union_left, lm_fockF_eq_sum f2 g _ Finset.subset_union_right, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lm_fockF_add {σ : Type*} (f1 f2 g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (f1 + f2) g = Formalism.REAL.fockF f1 g + Formalism.REAL.fockF f2 g := by
  classical
  rw [lm_fockF_eq_sum (f1 + f2) g (f1.support ∪ f2.support) MvPolynomial.support_add,
    lm_fockF_eq_sum f1 g _ Finset.subset_union_left, lm_fockF_eq_sum f2 g _ Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

/- English proof (translation)
Rewrite using `[lm_fockF_eq_sum (a • f) g f.support MvPolynomial.support_smul, Formalism.REAL.fockF, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lm_fockF_smul {σ : Type*} (a : ℂ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (a • f) g = a * Formalism.REAL.fockF f g := by
  classical
  rw [lm_fockF_eq_sum (a • f) g f.support MvPolynomial.support_smul, Formalism.REAL.fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[← Int.cast_smul_eq_zsmul ℂ, lm_fockF_smul]`.
-/
theorem lm_fockF_zsmul {σ : Type*} (a : ℤ) (f g : MvPolynomial σ ℂ) :
    Formalism.REAL.fockF (a • f) g = a * Formalism.REAL.fockF f g := by
  rw [← Int.cast_smul_eq_zsmul ℂ, lm_fockF_smul]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [Formalism.REAL.fockF]`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.sum_insert hi, lm_fockF_add, h0 i (Finset.mem_insert_self _ _), ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj)), add_zero]`.
-/
theorem lm_fockF_finsum {σ ι : Type*} (s : Finset ι) (y : ι → MvPolynomial σ ℂ) (g : MvPolynomial σ ℂ)
    (h0 : ∀ i ∈ s, Formalism.REAL.fockF (y i) g = 0) : Formalism.REAL.fockF (∑ i ∈ s, y i) g = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Formalism.REAL.fockF]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, lm_fockF_add, h0 i (Finset.mem_insert_self _ _),
      ih (fun j hj => h0 j (Finset.mem_insert_of_mem hj)), add_zero]

/- English proof (translation)
Simplify using `only [rowDiv, map_sub, Polynomial.coeff_sub]`.
-/
theorem lm_rowDiv_sub {R : Type*} [CommRing R] {r m : ℕ} (a b : Fin r) (k : ℕ)
    (f g : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b k (f - g) = rowDiv R a b k f - rowDiv R a b k g := by
  simp only [rowDiv, map_sub, Polynomial.coeff_sub]

/- English proof (translation)
Simplify using `only [rowDiv, map_smul, Polynomial.coeff_smul]`.
-/
theorem lm_rowDiv_smul {R : Type*} [CommRing R] {r m : ℕ} (a b : Fin r) (k : ℕ) (c : R)
    (f : MvPolynomial (Fin r × Fin m) R) :
    rowDiv R a b k (c • f) = c • rowDiv R a b k f := by
  simp only [rowDiv, map_smul, Polynomial.coeff_smul]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons x w ih => show rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (f - c • g)) = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) - c • rowDiv R x.1 x.2.1 x.2.2 (applyWord R w g)`. Rewrite using `[ih, lm_rowDiv_sub, lm_rowDiv_smul]`.
-/
theorem lm_applyWord_sub_smul {R : Type*} [CommRing R] {r m : ℕ} (w : List (Fin r × Fin r × ℕ)) (c : R)
    (f g : MvPolynomial (Fin r × Fin m) R) :
    applyWord R w (f - c • g) = applyWord R w f - c • applyWord R w g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show rowDiv R x.1 x.2.1 x.2.2 (applyWord R w (f - c • g)) =
      rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) - c • rowDiv R x.1 x.2.1 x.2.2 (applyWord R w g)
    rw [ih, lm_rowDiv_sub, lm_rowDiv_smul]

/- English proof (translation)
Introduce `m hm`. Apply `hf` to reduce the goal to its premises. Rewrite `hm` using `[coeff_map]`. Introduce `h0`. Apply `hm` to reduce the goal to its premises.

Rewrite using `[h0, map_zero]`.
-/
theorem lm_isWH_map {σ M : Type*} [AddCommMonoid M] (w : σ → M) (f : MvPolynomial σ ℤ) (d : M)
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w (map (Int.castRingHom ℂ) f) d := by
  intro m hm
  apply hf
  rw [coeff_map] at hm
  intro h0
  apply hm
  rw [h0, map_zero]

/- English proof (translation)
Introduce `m hm`. Rewrite using `[← hf hm, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `only [lastW, rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Fin.ext_iff]`. Distinguish the cases in `hv : v.1.1 + 1 = N`.

Rewrite using `[if_pos hv, if_pos (by omega)]`. Rewrite using `[if_neg hv, if_neg (by omega)]`.
-/
theorem lm_last_of_row {N : ℕ} (hN : 0 < N) (f : MvPolynomial (Fin N × Fin N) ℂ) (ω : Fin N → ℕ)
    (hf : IsWeightedHomogeneous (rowW N N) f ω) :
    IsWeightedHomogeneous (lastW N) f (ω ⟨N - 1, by omega⟩) := by
  intro m hm
  rw [← hf hm, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [lastW, rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Fin.ext_iff]
  by_cases hv : v.1.1 + 1 = N
  · rw [if_pos hv, if_pos (by omega)]
  · rw [if_neg hv, if_neg (by omega)]

/- English proof (translation)
Unfold `liftWt`. Rewrite using `[dif_neg (by simp; omega)]`.
-/
theorem lm_liftWt_last {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) (ω : Fin n → ℕ) :
    liftWt h lam mu ω ⟨N - 1, by omega⟩ = dLast lam mu := by
  unfold liftWt
  rw [dif_neg (by simp; omega)]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Use `congrFun he (eRow h a)` as an intermediate fact. Establish `ha : (eRow h a).1 < n` using `a.isLt`. Simplify using `only [liftWt, ha, dif_pos] at this`. Simplify `this` using `[eRow]`.
-/
theorem lm_liftWt_inj {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n) {ω ω' : Fin n → ℕ}
    (he : liftWt h lam mu ω = liftWt h lam mu ω') : ω = ω' := by
  funext a
  have := congrFun he (eRow h a)
  have ha : (eRow h a).1 < n := a.isLt
  simp only [liftWt, ha, dif_pos] at this
  simpa [eRow] using this

/- English proof (translation)
Unfold `initMinor`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `[RingHom.mapMatrix_apply]`.
-/
theorem lm_map_initMinor {r m s : ℕ} (I : Fin s → Fin r) (hs : s ≤ m) :
    map (Int.castRingHom ℂ) (initMinor ℤ (n := m) I hs) = initMinor ℂ I hs := by
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

/- English proof (translation)
Unfold `xi`. Simplify using `only [map_prod, map_mul, map_pow, lm_map_initMinor, Formalism.UG.P.wlocal_map_lpMinor]`.
-/
theorem lm_map_xi {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) :
    map (Int.castRingHom ℂ) (xi ℤ h lam sg) = xi ℂ h lam sg := by
  unfold xi
  simp only [map_prod, map_mul, map_pow, lm_map_initMinor, Formalism.UG.P.wlocal_map_lpMinor]

/- English proof (translation)
Unfold `extremal`. Conclude with `Formalism.UG.P.wlocal_map_hw _ _ _`.
-/
theorem lm_map_ext {n : ℕ} (sg : DomWeight n) :
    map (Int.castRingHom ℂ) (extremal ℤ n sg) = extremal ℂ n sg := by
  unfold extremal
  exact Formalism.UG.P.wlocal_map_hw _ _ _

/- English proof (translation)
Introduce `n N h lam sg hI io0 hE hx _hW`. Take `⟨Z, -, hZa⟩` from `hZ n N h lam sg hI`. Establish `hc0 : ((cBr h lam sg : ℤ) : ℂ) ≠ 0` using `Int.cast_ne_zero.mpr (hN n N h lam sg hI).1`. Use `set c : ℂ := ((cBr h lam sg : ℤ) : ℂ) with hc`. Establish `hxi0 : xi ℂ h lam sg ≠ 0` using `(hX n N h lam sg hI).1`.

Establish `hext : extremal ℂ n sg ∈ nablaSq ℂ n sg` using `hwMem ℂ n n le_rfl sg.natW (lm_natW_anti sg)`. Take `⟨hZmem, hZdiv, hZwt⟩` from `hZC n N h lam Z (fun mu hmu φ hφ => ⟨_, hZa mu hmu φ hφ⟩)`. Establish `hZio : ∀ s ∈ nablaSq ℂ n sg, Z (io0 s) = c • io0 s` using `fun s hs => hZa sg hI io0 hE s hs`. Establish `hO : ∀ o ∈ OtherPart h lam sg, Z o = 0`. Introduce `o ho`.

Establish `hle : OtherPart h lam sg ≤ LinearMap.ker Z`. Unfold `OtherPart`. Use `iSup_le fun mu => iSup_le fun hmu => iSup_le fun hne => iSup_le fun hw => iSup_le fun φ => iSup_le fun hφ => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Rewrite using `[LinearMap.mem_ker, hZa mu hmu φ hφ t ht, hV n N h lam sg mu hI hmu hne hw, Int.cast_zero, zero_smul]`.

Conclude with `hle ho`. Establish `hdec` using `hdecP n N h lam sg hI io0 hE (by rw [hx]; exact hxi0)`. Establish `hcrit : ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (lastW N) f (dLast lam sg) → ∀ s ∈ nablaSq ℂ n sg, Z f = c • io0 s → f - io0 s ∈ OtherPart h lam sg`. Introduce `f hf hfl s _ hZf`. Take `⟨u, hu, ho⟩` from `hdec f hf hfl`.

Establish `h1 : Z f = c • io0 u`. Use `hO _ ho` as an intermediate fact. Rewrite `this` using `[map_sub, hZio u hu, sub_eq_zero]`. Conclude with `this`. Establish `h2 : io0 u = io0 s`.

Rewrite `hZf` using `[h1]`. Conclude with `smul_right_injective _ hc0 hZf`. Rewrite using `[← h2]` and apply the resulting hypothesis. Establish `hZim : ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (lastW N) f (dLast lam sg) → ∃ u ∈ nablaSq ℂ n sg, Z f = io0 u`. Introduce `f hf hfl`.

Take `⟨u, hu, ho⟩` from `hdec f hf hfl`. Use `⟨c • u, Submodule.smul_mem _ _ hu, ?_⟩` and prove the remaining obligations. Use `hO _ ho` as an intermediate fact. Rewrite `this` using `[map_sub, hZio u hu, sub_eq_zero]`. Rewrite using `[this, map_smul]`.

Establish `hIoW : ∀ w : List (Fin n × Fin n × ℕ), OffDiag w → ∀ s ∈ nablaSq ℂ n sg, applyWord ℂ w s ∈ nablaSq ℂ n sg ∧ io0 (applyWord ℂ w s) = applyWord ℂ (liftWord h w) (io0 s)`. Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => intro _ s hs`. Conclude with `⟨hs, rfl⟩`.

Consider the case `cons x w ih`. Introduce `hw s hs`. Establish `hw' : OffDiag w` using `fun y hy => hw y (List.mem_cons_of_mem _ hy)`. Take `⟨h1, h2⟩` from `ih hw' s hs`. Use `⟨rowDivStable ℂ n n sg.natW x.1 x.2.1 x.2.2 _ h1, ?_⟩` and prove the remaining obligations.

Use `show io0 (rowDiv ℂ x.1 x.2.1 x.2.2 (applyWord ℂ w s)) = rowDiv ℂ (eRow h x.1) (eRow h x.2.1) x.2.2 (applyWord ℂ (liftWord h w) (io0 s))`. Rewrite using `[equivariant_divisibility n N h sg lam io0 hE x.1 x.2.1 (hw x (by simp)) x.2.2 _ h1, h2]`. Establish `hZW : ∀ w : List (Fin n × Fin n × ℕ), OffDiag w → ∀ f ∈ nablaSq ℂ N lam, applyWord ℂ (liftWord h w) f ∈ nablaSq ℂ N lam ∧ Z (applyWord ℂ (liftWord h w) f) = applyWord ℂ (liftWord h w) (Z f)`. Introduce `w`. Proceed by induction on `w with`.

Consider the case `nil => intro _ f hf`. Conclude with `⟨hf, rfl⟩`. Consider the case `cons x w ih`. Introduce `hw f hf`. Establish `hw' : OffDiag w` using `fun y hy => hw y (List.mem_cons_of_mem _ hy)`.

Take `⟨h1, h2⟩` from `ih hw' f hf`. Use `⟨rowDivStable ℂ N N lam.natW _ _ x.2.2 _ h1, ?_⟩` and prove the remaining obligations. Use `show Z (rowDiv ℂ (eRow h x.1) (eRow h x.2.1) x.2.2 (applyWord ℂ (liftWord h w) f)) = rowDiv ℂ (eRow h x.1) (eRow h x.2.1) x.2.2 (applyWord ℂ (liftWord h w) (Z f))`. Rewrite using `[hZdiv x.1 x.2.1 (hw x (by simp)) x.2.2 _ h1, h2]`. Establish `hgen : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n), shapeDeg sz = sg.natW → ∃ m ∈ nablaSq ℤ N lam, map (Int.castRingHom ℂ) m - io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz I)) ∈ OtherPart h lam sg`.

Introduce `K sz hsz I hsh`. Take `⟨M, hM1, hM2, hM3, J0, hJ0c, -, hJ0m⟩` from `tuple_decomposition_formula n N h lam sg hI K sz hsz hsh`. Establish `hbm : ∀ J, map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J) ∈ nablaSq ℂ n sg`. Introduce `J`. Use `bidetMem ℤ n n K sz hsz J` as an intermediate fact.

Rewrite `this` using `[hsh]`. Conclude with `dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW _ this`. Establish `hMm : ∀ J, map (Int.castRingHom ℂ) (M J) ∈ nablaSq ℂ N lam` using `fun J => dualWeylMap ℤ ℂ (Int.castRingHom ℂ) N N lam.natW _ (hM1 J).1`. Establish `hMl : ∀ J, IsWeightedHomogeneous (lastW N) (map (Int.castRingHom ℂ) (M J)) (dLast lam sg)`. Introduce `J`.

Use `lm_last_of_row (N := N) (by omega) _ _ (lm_isWH_map _ _ _ (hM1 J).2.1)` as an intermediate fact. Rewrite `this` using `[lm_liftWt_last]`. Then use the resulting hypothesis. Establish `hxiW : IsWeightedHomogeneous (rowW N N) (xi ℂ h lam sg) (liftWt h lam sg sg.natW)`. Use `lm_isWH_map _ _ _ (hM1 J0).2.1` as an intermediate fact. Rewrite `this` using `[hJ0m, lm_map_xi, hJ0c]`. Then use the resulting hypothesis.

Use `set Δ : (∀ k, Fin (sz k) → Fin n) → MvPolynomial (Fin N × Fin N) ℂ := fun J => Z (map (Int.castRingHom ℂ) (M J)) - c • io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J)) with hΔ`. Establish `hΔim : ∀ J, ∃ u ∈ nablaSq ℂ n sg, Δ J = io0 u`. Introduce `J`. Take `⟨u, hu, hZu⟩` from `hZim _ (hMm J) (hMl J)`. Use `⟨u - c • map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J), Submodule.sub_mem _ hu (Submodule.smul_mem _ _ (hbm J)), ?_⟩` and prove the remaining obligations.

Simplify using `only [hΔ]`. Rewrite using `[map_sub, map_smul, hZu]`. Establish `hΔorth : ∀ J, Formalism.REAL.fockF (Δ J) (xi ℂ h lam sg) = 0`. Introduce `J`. Distinguish the cases in `hJ : tupCnt J = sg.natW`.

Take `⟨ε, hb, hm⟩` from `hM3 J hJ`. Establish `h0 : Δ J = 0`. Simplify using `only [hΔ, hb, hm, map_zsmul, lm_map_xi, lm_map_ext]`. Rewrite using `[← hx, hZio _ hext, smul_comm c ε, sub_self]`. Rewrite using `[h0]`.

Simplify using `[Formalism.REAL.fockF]`. Establish `hw1 : IsWeightedHomogeneous (rowW N N) (Δ J) (liftWt h lam sg (tupCnt J))`. Establish `a1` using `hZwt _ _ (hMm J) (lm_isWH_map _ _ _ (hM1 J).2.1)`. Establish `a2` using `equivariant_partial_weight n N h lam sg hI io0 hE (tupCnt J) _ (hbm J) (lm_isWH_map _ _ _ (hM1 J).2.2)`. Use `Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr a1) (Submodule.smul_mem _ c ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr a2))` as an intermediate fact.

Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).mp this`. Conclude with `fockWeightOrth _ _ (rowW N N) _ _ _ _ (fun he => hJ (lm_liftWt_inj h lam sg he)) hw1 hxiW`. Take `⟨u, hu, hΔu⟩` from `hΔim I`. Establish `hzero : io0 u = 0`. Use `hFD n N h lam sg hI io0 hE hx u hu ?_` and prove the remaining obligations.

Introduce `w hw`. Take `⟨d, hd1, hd2⟩` from `hM2 I w hw`. Rewrite using `[← hΔu]`. Establish `e1 : applyWord ℂ (liftWord h w) (Z (map (Int.castRingHom ℂ) (M I))) = d.sum fun J k => k • Z (map (Int.castRingHom ℂ) (M J))`. Rewrite using `[← (hZW w hw _ (hMm I)).2, ← Formalism.UG.P.wlocal_map_applyWord, hd2, Finsupp.sum, Finsupp.sum, map_sum, map_sum]`.

Simplify using `only [map_zsmul]`. Establish `e2 : applyWord ℂ (liftWord h w) (io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz I))) = d.sum fun J k => k • io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J))`. Rewrite using `[← (hIoW w hw _ (hbm I)).2, ← Formalism.UG.P.wlocal_map_applyWord, hd1, Finsupp.sum, Finsupp.sum, map_sum, map_sum]`. Simplify using `only [map_zsmul]`. Establish `e3 : applyWord ℂ (liftWord h w) (Δ I) = ∑ J ∈ d.support, d J • Δ J`.

Simplify using `only [hΔ]`. Rewrite using `[lm_applyWord_sub_smul, e1, e2, Finsupp.sum, Finsupp.sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations. Rewrite using `[smul_sub, smul_comm c (d J)]`. Rewrite using `[e3]`.

Use `lm_fockF_finsum _ _ _ fun J _ => ?_` and prove the remaining obligations. Rewrite using `[lm_fockF_zsmul, hΔorth J, mul_zero]`. Use `⟨M I, (hM1 I).1, hcrit _ (hMm I) (hMl I) _ (hbm I) ?_⟩` and prove the remaining obligations. Establish `: Δ I = 0` using `by rw [hΔu, hzero]`. Rewrite `this` using `[hΔ]`.

Conclude with `sub_eq_zero.mp this`. Introduce `s hs`. Establish `hs' : s ∈ Submodule.span ℤ {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n), shapeDeg sz = sg.natW ∧ f = bideterminant ℤ sz hsz I}`. Rewrite using `[← standardMonomialSpan n n sg.natW (lm_natW_anti sg)]`. Conclude with `hs`.

Use `clear hs`. Proceed by induction on `hs' using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨K, sz, hsz, I, hsh, rfl⟩` from `hx`. Conclude with `hgen K sz hsz I hsh`.

Consider the case `zero => exact ⟨0, Submodule.zero_mem _, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨m1, hm1, h1⟩` from `hx`. Take `⟨m2, hm2, h2⟩` from `hy`. Use `⟨m1 + m2, Submodule.add_mem _ hm1 hm2, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add, map_add, map_add]`. Use `Submodule.add_mem _ h1 h2 using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Consider the case `smul a x _ hx`. Take `⟨m, hm, h1⟩` from `hx`.

Use `⟨a • m, Submodule.smul_mem _ a hm, ?_⟩` and prove the remaining obligations. Rewrite using `[map_zsmul, map_zsmul, map_zsmul, ← smul_sub]`. Conclude with `zsmul_mem h1 a`.
-/
theorem liftMod_asm (hZ : CapelliZ) (hV : ZScalarVanish) (hN : Numbers) (hX : XiFacts)
    (equivariant_divisibility : EqvDiv) (equivariant_partial_weight : EqvRowWt) (hdecP : Decomp) (hZC : ZComm) (hFD : FockDetect)
    (tuple_decomposition_formula : TupleCore) : LiftMod := by
  intro n N h lam sg hI io0 hE hx _hW
  obtain ⟨Z, -, hZa⟩ := hZ n N h lam sg hI
  have hc0 : ((cBr h lam sg : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (hN n N h lam sg hI).1
  set c : ℂ := ((cBr h lam sg : ℤ) : ℂ) with hc
  have hxi0 : xi ℂ h lam sg ≠ 0 := (hX n N h lam sg hI).1
  have hext : extremal ℂ n sg ∈ nablaSq ℂ n sg := hwMem ℂ n n le_rfl sg.natW (lm_natW_anti sg)
  obtain ⟨hZmem, hZdiv, hZwt⟩ := hZC n N h lam Z
    (fun mu hmu φ hφ => ⟨_, hZa mu hmu φ hφ⟩)
  have hZio : ∀ s ∈ nablaSq ℂ n sg, Z (io0 s) = c • io0 s := fun s hs => hZa sg hI io0 hE s hs
  have hO : ∀ o ∈ OtherPart h lam sg, Z o = 0 := by
    intro o ho
    have hle : OtherPart h lam sg ≤ LinearMap.ker Z := by
      unfold OtherPart
      refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun hne => iSup_le fun hw =>
        iSup_le fun φ => iSup_le fun hφ => ?_
      rintro _ ⟨t, ht, rfl⟩
      rw [LinearMap.mem_ker, hZa mu hmu φ hφ t ht, hV n N h lam sg mu hI hmu hne hw, Int.cast_zero,
        zero_smul]
    exact hle ho
  have hdec := hdecP n N h lam sg hI io0 hE (by rw [hx]; exact hxi0)
  have hcrit : ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (lastW N) f (dLast lam sg) →
      ∀ s ∈ nablaSq ℂ n sg, Z f = c • io0 s → f - io0 s ∈ OtherPart h lam sg := by
    intro f hf hfl s _ hZf
    obtain ⟨u, hu, ho⟩ := hdec f hf hfl
    have h1 : Z f = c • io0 u := by
      have := hO _ ho
      rw [map_sub, hZio u hu, sub_eq_zero] at this
      exact this
    have h2 : io0 u = io0 s := by
      rw [h1] at hZf
      exact smul_right_injective _ hc0 hZf
    rwa [← h2]
  have hZim : ∀ f ∈ nablaSq ℂ N lam, IsWeightedHomogeneous (lastW N) f (dLast lam sg) →
      ∃ u ∈ nablaSq ℂ n sg, Z f = io0 u := by
    intro f hf hfl
    obtain ⟨u, hu, ho⟩ := hdec f hf hfl
    refine ⟨c • u, Submodule.smul_mem _ _ hu, ?_⟩
    have := hO _ ho
    rw [map_sub, hZio u hu, sub_eq_zero] at this
    rw [this, map_smul]
  have hIoW : ∀ w : List (Fin n × Fin n × ℕ), OffDiag w → ∀ s ∈ nablaSq ℂ n sg,
      applyWord ℂ w s ∈ nablaSq ℂ n sg ∧
        io0 (applyWord ℂ w s) = applyWord ℂ (liftWord h w) (io0 s) := by
    intro w
    induction w with
    | nil => intro _ s hs; exact ⟨hs, rfl⟩
    | cons x w ih =>
      intro hw s hs
      have hw' : OffDiag w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
      obtain ⟨h1, h2⟩ := ih hw' s hs
      refine ⟨rowDivStable ℂ n n sg.natW x.1 x.2.1 x.2.2 _ h1, ?_⟩
      show io0 (rowDiv ℂ x.1 x.2.1 x.2.2 (applyWord ℂ w s)) =
        rowDiv ℂ (eRow h x.1) (eRow h x.2.1) x.2.2 (applyWord ℂ (liftWord h w) (io0 s))
      rw [equivariant_divisibility n N h sg lam io0 hE x.1 x.2.1 (hw x (by simp)) x.2.2 _ h1, h2]
  have hZW : ∀ w : List (Fin n × Fin n × ℕ), OffDiag w → ∀ f ∈ nablaSq ℂ N lam,
      applyWord ℂ (liftWord h w) f ∈ nablaSq ℂ N lam ∧
        Z (applyWord ℂ (liftWord h w) f) = applyWord ℂ (liftWord h w) (Z f) := by
    intro w
    induction w with
    | nil => intro _ f hf; exact ⟨hf, rfl⟩
    | cons x w ih =>
      intro hw f hf
      have hw' : OffDiag w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
      obtain ⟨h1, h2⟩ := ih hw' f hf
      refine ⟨rowDivStable ℂ N N lam.natW _ _ x.2.2 _ h1, ?_⟩
      show Z (rowDiv ℂ (eRow h x.1) (eRow h x.2.1) x.2.2 (applyWord ℂ (liftWord h w) f)) =
        rowDiv ℂ (eRow h x.1) (eRow h x.2.1) x.2.2 (applyWord ℂ (liftWord h w) (Z f))
      rw [hZdiv x.1 x.2.1 (hw x (by simp)) x.2.2 _ h1, h2]
  have hgen : ∀ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin n),
      shapeDeg sz = sg.natW → ∃ m ∈ nablaSq ℤ N lam,
        map (Int.castRingHom ℂ) m - io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz I)) ∈
          OtherPart h lam sg := by
    intro K sz hsz I hsh
    obtain ⟨M, hM1, hM2, hM3, J0, hJ0c, -, hJ0m⟩ := tuple_decomposition_formula n N h lam sg hI K sz hsz hsh
    have hbm : ∀ J, map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J) ∈ nablaSq ℂ n sg := by
      intro J
      have := bidetMem ℤ n n K sz hsz J
      rw [hsh] at this
      exact dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW _ this
    have hMm : ∀ J, map (Int.castRingHom ℂ) (M J) ∈ nablaSq ℂ N lam := fun J =>
      dualWeylMap ℤ ℂ (Int.castRingHom ℂ) N N lam.natW _ (hM1 J).1
    have hMl : ∀ J, IsWeightedHomogeneous (lastW N) (map (Int.castRingHom ℂ) (M J)) (dLast lam sg) := by
      intro J
      have := lm_last_of_row (N := N) (by omega) _ _ (lm_isWH_map _ _ _ (hM1 J).2.1)
      rwa [lm_liftWt_last] at this
    have hxiW : IsWeightedHomogeneous (rowW N N) (xi ℂ h lam sg) (liftWt h lam sg sg.natW) := by
      have := lm_isWH_map _ _ _ (hM1 J0).2.1
      rwa [hJ0m, lm_map_xi, hJ0c] at this

    set Δ : (∀ k, Fin (sz k) → Fin n) → MvPolynomial (Fin N × Fin N) ℂ := fun J =>
      Z (map (Int.castRingHom ℂ) (M J)) - c • io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J)) with hΔ
    have hΔim : ∀ J, ∃ u ∈ nablaSq ℂ n sg, Δ J = io0 u := by
      intro J
      obtain ⟨u, hu, hZu⟩ := hZim _ (hMm J) (hMl J)
      refine ⟨u - c • map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J),
        Submodule.sub_mem _ hu (Submodule.smul_mem _ _ (hbm J)), ?_⟩
      simp only [hΔ]
      rw [map_sub, map_smul, hZu]
    have hΔorth : ∀ J, Formalism.REAL.fockF (Δ J) (xi ℂ h lam sg) = 0 := by
      intro J
      by_cases hJ : tupCnt J = sg.natW
      · obtain ⟨ε, hb, hm⟩ := hM3 J hJ
        have h0 : Δ J = 0 := by
          simp only [hΔ, hb, hm, map_zsmul, lm_map_xi, lm_map_ext]
          rw [← hx, hZio _ hext, smul_comm c ε, sub_self]
        rw [h0]
        simp [Formalism.REAL.fockF]
      · have hw1 : IsWeightedHomogeneous (rowW N N) (Δ J) (liftWt h lam sg (tupCnt J)) := by
          have a1 := hZwt _ _ (hMm J) (lm_isWH_map _ _ _ (hM1 J).2.1)
          have a2 := equivariant_partial_weight n N h lam sg hI io0 hE (tupCnt J) _ (hbm J)
            (lm_isWH_map _ _ _ (hM1 J).2.2)
          have := Submodule.sub_mem _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr a1)
            (Submodule.smul_mem _ c ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr a2))
          exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp this
        exact fockWeightOrth _ _ (rowW N N) _ _ _ _
          (fun he => hJ (lm_liftWt_inj h lam sg he)) hw1 hxiW
    obtain ⟨u, hu, hΔu⟩ := hΔim I
    have hzero : io0 u = 0 := by
      refine hFD n N h lam sg hI io0 hE hx u hu ?_
      intro w hw
      obtain ⟨d, hd1, hd2⟩ := hM2 I w hw
      rw [← hΔu]
      have e1 : applyWord ℂ (liftWord h w) (Z (map (Int.castRingHom ℂ) (M I))) =
          d.sum fun J k => k • Z (map (Int.castRingHom ℂ) (M J)) := by
        rw [← (hZW w hw _ (hMm I)).2, ← Formalism.UG.P.wlocal_map_applyWord, hd2, Finsupp.sum, Finsupp.sum,
          map_sum, map_sum]
        simp only [map_zsmul]
      have e2 : applyWord ℂ (liftWord h w) (io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz I))) =
          d.sum fun J k => k • io0 (map (Int.castRingHom ℂ) (bideterminant ℤ sz hsz J)) := by
        rw [← (hIoW w hw _ (hbm I)).2, ← Formalism.UG.P.wlocal_map_applyWord, hd1, Finsupp.sum, Finsupp.sum,
          map_sum, map_sum]
        simp only [map_zsmul]
      have e3 : applyWord ℂ (liftWord h w) (Δ I) = ∑ J ∈ d.support, d J • Δ J := by
        simp only [hΔ]
        rw [lm_applyWord_sub_smul, e1, e2, Finsupp.sum, Finsupp.sum, Finset.smul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [smul_sub, smul_comm c (d J)]
      rw [e3]
      refine lm_fockF_finsum _ _ _ fun J _ => ?_
      rw [lm_fockF_zsmul, hΔorth J, mul_zero]
    refine ⟨M I, (hM1 I).1, hcrit _ (hMm I) (hMl I) _ (hbm I) ?_⟩
    have : Δ I = 0 := by rw [hΔu, hzero]
    rw [hΔ] at this
    exact sub_eq_zero.mp this
  intro s hs
  have hs' : s ∈ Submodule.span ℤ {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
      (I : ∀ k, Fin (sz k) → Fin n), shapeDeg sz = sg.natW ∧ f = bideterminant ℤ sz hsz I} := by
    rw [← standardMonomialSpan n n sg.natW (lm_natW_anti sg)]
    exact hs
  clear hs
  induction hs' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, hsh, rfl⟩ := hx
    exact hgen K sz hsz I hsh
  | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, hm1, h1⟩ := hx
    obtain ⟨m2, hm2, h2⟩ := hy
    refine ⟨m1 + m2, Submodule.add_mem _ hm1 hm2, ?_⟩
    rw [map_add, map_add, map_add]
    convert Submodule.add_mem _ h1 h2 using 1
    abel
  | smul a x _ hx =>
    obtain ⟨m, hm, h1⟩ := hx
    refine ⟨a • m, Submodule.smul_mem _ a hm, ?_⟩
    rw [map_zsmul, map_zsmul, map_zsmul, ← smul_sub]
    exact zsmul_mem h1 a

end PI.WGL
