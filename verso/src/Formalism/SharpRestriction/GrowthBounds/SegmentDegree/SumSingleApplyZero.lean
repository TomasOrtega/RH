import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DplusLeBeS

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

/- English proof (translation)
Rewrite `hP`, the goal using `[mem_supported]`. Introduce `v hv`. Establish `h1` using `vars_rename f P (Finset.mem_coe.mp hv)`. Take `⟨u, hu, rfl⟩` from `Finset.mem_image.mp h1`. Conclude with `h u (hP (Finset.mem_coe.mpr hu))`.
-/
theorem rename_mem_supported {R σ τ : Type} [CommRing R] {f : σ → τ} {S : Set σ} {S' : Set τ}
    (h : ∀ v ∈ S, f v ∈ S') {P : MvPolynomial σ R} (hP : P ∈ supported R S) : rename f P ∈ supported R S' := by
  classical
  rw [mem_supported] at hP ⊢
  intro v hv
  have h1 := vars_rename f P (Finset.mem_coe.mp hv)
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h1
  exact h u (hP (Finset.mem_coe.mpr hu))

/- English proof (translation)
Rewrite using `[Finsupp.finsetSum_apply]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply, if_neg (h i hi)]`.
-/
theorem sum_single_apply_zero {σ ι : Type} (s : Finset ι) (a : ι → σ) (k : ι → ℕ) (v : σ) (h : ∀ i ∈ s, a i ≠ v) :
    (∑ i ∈ s, Finsupp.single (a i) (k i)) v = 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finsupp.single_apply, if_neg (h i hi)]

section Fin7

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (K : ℕ)

def gp (j : ℤ) : Fin (segN X.F j) × Fin r → ℤ × Fin (r + K) := fun v => (segE X.F j v.1, Fin.castAdd K v.2)

def gt (j : ℤ) : Fin (segN X.F j) × Fin K → ℤ × Fin (r + K) := fun v => (segE X.F j v.1, Fin.natAdd r v.2)

/- English proof (translation)
Unfold `segRen PsiPl`. Rewrite using `[rename_rename]`. Both sides reduce to the same expression.
-/
theorem segRen_PsiPl (O : Type) [CommRing O] (j : ℤ) (ν : Fin (segN X.F j + 1) → Fin r → ℤ)
    (I : ℤ → Finset (Fin r)) :
    segRen X.F j O (r + K) (PsiPl O ν I) = rename (gp X K j) (Psi O ν I) := by
  unfold segRen PsiPl
  rw [rename_rename]
  rfl

/- English proof (translation)
Unfold `segRen PsiTan`. Rewrite using `[rename_rename]`. Both sides reduce to the same expression.
-/
theorem segRen_PsiTan (O : Type) [CommRing O] (j : ℤ) (κ : Fin (segN X.F j + 1) → Fin K → ℤ)
    (I : ℤ → Finset (Fin K)) :
    segRen X.F j O (r + K) (PsiTan O κ I) = rename (gt X K j) (Psi O κ I) := by
  unfold segRen PsiTan
  rw [rename_rename]
  rfl

def tauSet (j : ℤ) : Set (ℤ × Fin (r + K)) := {v | ∃ t c : Fin r, v = (X.F.fr j t.val, Fin.castAdd K c)}

/- English proof (translation)
Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [Fin.val_castAdd, Fin.val_natAdd] at this`. Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem castAdd_ne_natAdd (a : Fin r) (c : Fin K) : Fin.castAdd K a ≠ Fin.natAdd r c := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  have := a.isLt
  omega

/- English proof (translation)
Establish `hrN` using `k_r_le_segN X.F hV (NeZero.pos r) j`. Use extensionality with `v`. Establish `hv1` using `v.1.isLt`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, c, hc, hv⟩`.

Simplify using `only [gp, Prod.mk.injEq] at hv`. Establish `h1` using `(segE_eq_fr_iff X.F hV j v.1 t.isLt).mp hv.1`. Establish `h2 : v.2 = c` using `Fin.castAdd_injective _ _ hv.2`. Use `⟨by omega, fun h3 => hc ?_⟩` and prove the remaining obligations. Apply `Fin.ext` to reduce the goal to its premises.

Rewrite using `[Fin.val_rev, ← h2]`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨h1, h2⟩`. Establish `ht : v.1.val - (segN X.F j - r) < r` using `by omega`. Use `⟨⟨v.1.val - (segN X.F j - r), ht⟩, v.2, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h3`. Apply `h2` to reduce the goal to its premises. Use `congrArg Fin.val h3` as an intermediate fact. Rewrite `this` using `[Fin.val_rev]`. Simplify using `only [] at this`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [gp, Prod.mk.injEq, and_true]`. Conclude with `(segE_eq_fr_iff X.F hV j v.1 ht).mpr (by omega)`.
-/
theorem gp_preimage {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ) :
    (gp X K j) ⁻¹' (X.offSet K j) = offN (segN X.F j - r) := by
  have hrN := k_r_le_segN X.F hV (NeZero.pos r) j
  ext v
  have hv1 := v.1.isLt
  constructor
  · rintro ⟨t, c, hc, hv⟩
    simp only [gp, Prod.mk.injEq] at hv
    have h1 := (segE_eq_fr_iff X.F hV j v.1 t.isLt).mp hv.1
    have h2 : v.2 = c := Fin.castAdd_injective _ _ hv.2
    refine ⟨by omega, fun h3 => hc ?_⟩
    apply Fin.ext
    rw [Fin.val_rev, ← h2]
    omega
  · rintro ⟨h1, h2⟩
    have ht : v.1.val - (segN X.F j - r) < r := by omega
    refine ⟨⟨v.1.val - (segN X.F j - r), ht⟩, v.2, ?_, ?_⟩
    · intro h3
      apply h2
      have := congrArg Fin.val h3
      rw [Fin.val_rev] at this
      simp only [] at this
      omega
    · simp only [gp, Prod.mk.injEq, and_true]
      exact (segE_eq_fr_iff X.F hV j v.1 ht).mpr (by omega)

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨t, c, -, hv⟩`. Simplify using `only [gt, Prod.mk.injEq] at hv`. Conclude with `castAdd_ne_natAdd K c v.2 hv.2.symm`.
-/
theorem gt_preimage (j : ℤ) : (gt X K j) ⁻¹' (X.offSet K j) = ∅ := by
  ext v
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  rintro ⟨t, c, -, hv⟩
  simp only [gt, Prod.mk.injEq] at hv
  exact castAdd_ne_natAdd K c v.2 hv.2.symm

def dgT (j : ℤ) (n0 : ℕ) (hN : n0 + r = segN X.F j) (be : ℤ) (ν : Fin (segN X.F j + 1) → Fin r → ℤ) :
    ℤ × Fin (r + K) →₀ ℕ :=
  ∑ c ∈ Finset.Icc 1 be, ∑ m ∈ riseA n0 ν c r, Finsupp.single (gp X K j (tauI n0 hN m, m)) 1

/- English proof (translation)
Take `⟨e, he⟩` from `kill_Psi (R := O) hN H`. Use `⟨e, ?_⟩` and prove the remaining obligations. Unfold `Dat.wordEl`. Rewrite using `[map_mul, map_mul, map_mul, segRen_PsiPl, segRen_PsiTan, segRen_PsiPl, kill_rename, kill_rename, gp_preimage X K hV j, kill_of_empty _ (gt_preimage X K j), he]`. Simplify using `only [map_mul, map_pow, map_neg, map_one, map_prod, rename_X]`.

Unfold `dgT`. Rewrite using `[MvPolynomial.monomial_sum_one]`. Establish `: ∀ c ∈ Finset.Icc 1 be, monomial (∑ m ∈ riseA (segN X.F j - r) (plPart q.1) c r, Finsupp.single (gp X K j (tauI (segN X.F j - r) hN m, m)) 1) (1 : O) = ∏ m ∈ riseA (segN X.F j - r) (plPart q.1) c r, MvPolynomial.X (gp X K j (tauI (segN X.F j - r) hN m, m))`. Introduce `c _`. Rewrite using `[MvPolynomial.monomial_sum_one]`.

Both sides reduce to the same expression. Rewrite using `[Finset.prod_congr rfl this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kill_wordEl (O : Type) [CommRing O] {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ)
    (hN : segN X.F j - r + r = segN X.F j) (be : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ))
    (H : PlHyp (segN X.F j - r) be (plPart q.1)) :
    ∃ e : ℕ, kill (X.offSet K j) (X.wordEl K O j q) =
      (-1) ^ e * monomial (dgT X K j (segN X.F j - r) hN be (plPart q.1)) (1 : O) *
        segRen X.F j O (r + K) (PsiPl O (cutPath (segN X.F j - r) (plPart q.1)) (Icut (segN X.F j - r) (plPart q.1)) *
          PsiTan O (tanPart q.1) q.2.1) := by
  classical
  obtain ⟨e, he⟩ := kill_Psi (R := O) hN H
  refine ⟨e, ?_⟩
  unfold Dat.wordEl
  rw [map_mul, map_mul, map_mul, segRen_PsiPl, segRen_PsiTan, segRen_PsiPl, kill_rename, kill_rename,
    gp_preimage X K hV j, kill_of_empty _ (gt_preimage X K j), he]
  simp only [map_mul, map_pow, map_neg, map_one, map_prod, rename_X]
  unfold dgT
  rw [MvPolynomial.monomial_sum_one]
  have : ∀ c ∈ Finset.Icc 1 be,
      monomial (∑ m ∈ riseA (segN X.F j - r) (plPart q.1) c r,
        Finsupp.single (gp X K j (tauI (segN X.F j - r) hN m, m)) 1) (1 : O) =
      ∏ m ∈ riseA (segN X.F j - r) (plPart q.1) c r, MvPolynomial.X (gp X K j (tauI (segN X.F j - r) hN m, m)) := by
    intro c _
    rw [MvPolynomial.monomial_sum_one]
    rfl
  rw [Finset.prod_congr rfl this]
  ring

/- English proof (translation)
Unfold `Dat.monTau`. Rewrite using `[Finsupp.finsetSum_apply, Finset.sum_eq_single (t, c)]`. Simplify using the standard rewrite rules. Introduce `v _ hv`. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `hv (Prod.ext (fr_injective X.F hV j h.1) (Fin.castAdd_injective _ _ h.2))`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem monTau_apply {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ) (u : Fin r × Fin r → ℕ) (t c : Fin r) :
    X.monTau K j u (X.F.fr j t.val, Fin.castAdd K c) = u (t, c) := by
  classical
  unfold Dat.monTau
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (t, c)]
  · simp
  · intro v _ hv
    rw [Finsupp.single_apply, if_neg]
    intro h
    simp only [Prod.mk.injEq] at h
    exact hv (Prod.ext (fr_injective X.F hV j h.1) (Fin.castAdd_injective _ _ h.2))
  · intro h; exact absurd (Finset.mem_univ _) h

end Fin7

/- English proof (translation)
Introduce `p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hB`. Establish `: Fact p.Prime` using `⟨hX.prime⟩`. Establish `hr : 0 < r` using `NeZero.pos r`. Establish `hV` using `hX.valid`. Establish `hrN` using `k_r_le_segN X.F hV hr j`.

Establish `hNK : segN X.F j + r ≤ K` using `le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK`. Establish `hN : segN X.F j - r + r = segN X.F j` using `Nat.sub_add_cancel hrN`. Establish `h10 : BracketPolynomialSpan D` using `hAdm.2.2.2.2.2.2.2.2.2.1`. Establish `h12 : NestedTypeBound D` using `hAdm.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hw` using `(h12 p O S n' r K X.F X.L₁ X.N₁ j (fun _ => 0) (fun _ => 0) (fun _ => 0) hV hNK (fun _ => le_rfl)).2.1`.

Establish `hH : ∀ q : X.Idx p K j (X.restr j b), PlHyp (segN X.F j - r) (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)`. Introduce `q`. Take `⟨dd, hP, -⟩` from `q.2`. Conclude with `plHyp_of X p K hX j _ _ dd hP`. Establish `hpair : ∀ q : X.Idx p K j (X.restr j b), ∃ b' b'' : Fin (segN X.F j) → ℕ, (∃ P1 : PPath r (segN X.F j) (segLL X.F j) b', P1.mu = plPart q.1.1) ∧ (∃ P2 : PPath K (segN X.F j) (segLL X.F j) b'', P2.mu = tanPart q.1.1)`.

Introduce `q`. Take `⟨dd, hP, -⟩` from `q.2`. Take `⟨P, hPμ⟩` from `hP.path`. Take `⟨b', b'', -, h1, h2, -⟩` from `(h10 (segN X.F j) r K (segLL X.F j) dd hNK (plPart q.1.1) (tanPart q.1.1)).mp ⟨P, by rw [hPμ, joinPT_parts]⟩`. Conclude with `⟨b', b'', h1, h2⟩`.

Establish `hx : ∀ q : X.Idx p K j (X.restr j b), ((cutPath (segN X.F j - r) (plPart q.1.1), tanPart q.1.1) ∈ segPairsAll X.F j K) ∧ IsSt (cutPath (segN X.F j - r) (plPart q.1.1)) (Icut (segN X.F j - r) (plPart q.1.1)) ∧ IsSt (tanPart q.1.1) q.1.2.1`. Introduce `q`. Take `⟨b', b'', ⟨P1, h1⟩, h2⟩` from `hpair q`. Take `⟨bc, Pc, hPc⟩` from `cut_ppath P1 (segN X.F j - r)`. Take `⟨dd, -, -, hSt, -⟩` from `q.2`.

Conclude with `⟨⟨bc, b'', ⟨Pc, by rw [hPc, h1]⟩, h2⟩, isSt_cut hN (hH q), hSt⟩`. Set `x : X.Idx p K j (X.restr j b) → {x : ((Fin (segN X.F j + 1) → Fin r → ℤ) × (Fin (segN X.F j + 1) → Fin K → ℤ)) × ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) // x.1 ∈ segPairsAll X.F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2}` to `fun q => ⟨((cutPath (segN X.F j - r) (plPart q.1.1), tanPart q.1.1), (Icut (segN X.F j - r) (plPart q.1.1), q.1.2.1)), hx q⟩`. Set `M : X.Idx p K j (X.restr j b) → (ℤ × Fin (r + K) →₀ ℕ)` to `fun q => X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)`. Establish `htauI : ∀ m : Fin r, gp X K j (tauI (segN X.F j - r) hN m, m) ∈ tauSet X K j`. Introduce `m`.

Establish `hm` using `m.isLt`. Use `⟨⟨r - 1 - m.val, by omega⟩, m, ?_⟩` and prove the remaining obligations. Simplify using `only [gp, Prod.mk.injEq, and_true]`. Conclude with `(segE_eq_fr_iff X.F hV j _ (by omega)).mpr rfl`. Establish `hM : ∀ q, ∀ v, M q v ≠ 0 → v ∈ tauSet X K j`.

Introduce `q v hv`. Assume the negation of the conclusion as `hnot`. Apply `hv` to reduce the goal to its premises. Use `show (X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q.1.1)) v = 0`. Rewrite using `[Finsupp.add_apply]`.

Establish `h1 : X.monTau K j q.1.2.2 v = 0`. Unfold `Dat.monTau`. Conclude with `sum_single_apply_zero _ _ _ v fun i _ h => hnot ⟨i.1, i.2, h.symm⟩`. Establish `h2 : dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) v = 0`. Unfold `dgT`.

Rewrite using `[Finsupp.finsetSum_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Conclude with `sum_single_apply_zero _ _ _ v fun m _ h => hnot (h ▸ htauI m)`. Rewrite using `[h1, h2]`. Establish `hsup : ∀ q, segRen X.F j O (r + K) (PsiPl O (x q).1.1.1 (x q).1.2.1 * PsiTan O (x q).1.1.2 (x q).1.2.2) ∈ supported O (tauSet X K j)ᶜ`.

Introduce `q`. Rewrite using `[map_mul, segRen_PsiPl, segRen_PsiTan]`. Use `Subalgebra.mul_mem _ ?_ ?_` and prove the remaining obligations. Use `rename_mem_supported ?_ (Psi_cut_supported (segN X.F j - r) (by omega) (plPart q.1.1) _)` and prove the remaining obligations. Introduce and unpack `v hv ⟨t, c, h⟩`.

Simplify using `only [gp, Prod.mk.injEq] at h`. Use `(segE_eq_fr_iff X.F hV j v.1 t.isLt).mp h.1` as an intermediate fact. Establish `hv' : v.1.val < segN X.F j - r` using `hv`. Use linear arithmetic over natural numbers and integers. Use `rename_mem_supported (S := Set.univ) ?_ (by rw [supported_univ]; exact Algebra.mem_top)` and prove the remaining obligations.

Introduce and unpack `v - ⟨t, c, h⟩`. Simplify using `only [gt, Prod.mk.injEq] at h`. Conclude with `castAdd_ne_natAdd K c v.2 h.2.symm`. Establish `hinj : ∀ q q', M q = M q' → x q = x q' → q = q'`. Introduce `q q' hMq hxq`.

Establish `hx'` using `congrArg Subtype.val hxq`. Simplify using `only [x, Prod.mk.injEq] at hx'`. Take `⟨⟨hcut, hκ⟩, hI, hI''⟩` from `hx'`. Take `⟨b1, -, ⟨P1, h1⟩, -⟩` from `hpair q`. Take `⟨b2, -, ⟨P2, h2⟩, -⟩` from `hpair q'`.

Establish `hν : plPart q.1.1 = plPart q'.1.1` using `path_eq_of_cut hN (hH q) (hH q') (fun i => by rw [← h1]; exact P1.dom i) (fun i => by rw [← h2]; exact P2.dom i) hcut hI`. Establish `hμ : q.1.1 = q'.1.1`. Rewrite using `[← joinPT_parts q.1.1, ← joinPT_parts q'.1.1, hν, hκ]`. Establish `hu0 : X.monTau K j q.1.2.2 = X.monTau K j q'.1.2.2`. Establish `h3 : X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q.1.1) = X.monTau K j q'.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q'.1.1)` using `hMq`.

Rewrite `h3` using `[hν]`. Conclude with `add_right_cancel h3`. Establish `hu : q.1.2.2 = q'.1.2.2`. Use function extensionality and compare the values at `v`. Rewrite using `[← monTau_apply X K hV j q.1.2.2 v.1 v.2, ← monTau_apply X K hV j q'.1.2.2 v.1 v.2, hu0]`.

Conclude with `Subtype.ext (Prod.ext hμ (Prod.ext hI'' hu))`. Establish `hli` using `li_mono_words (tauSet X K j) _ hw M x hM hsup hinj`. Establish `hkill` using `fun q : X.Idx p K j (X.restr j b) => kill_wordEl X K O hV j hN (X.beS p K j (X.restr j b) : ℤ) q.1 (hH q)`. Use `choose e he using hkill`. Establish `hli2` using `hli.units_smul fun q => (-1 : Oˣ) ^ e q`.

Establish `heq : (fun q : X.Idx p K j (X.restr j b) => monomial (X.monTau K j q.1.2.2) (1 : O) * kill (X.offSet K j) (X.wordEl K O j q.1)) = ((fun q => (-1 : Oˣ) ^ e q) • fun q => monomial (M q) (1 : O) * segRen X.F j O (r + K) (PsiPl O (x q).1.1.1 (x q).1.2.1 * PsiTan O (x q).1.1.2 (x q).1 …`. Use function extensionality and compare the values at `q`. Rewrite using `[he q]`. Simplify using `only [Pi.smul_apply']`. Rewrite using `[Units.smul_def, MvPolynomial.smul_eq_C_mul]`.

Establish `hmm : monomial (M q) (1 : O) = monomial (X.monTau K j q.1.2.2) (1 : O) * monomial (dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)) (1 : O)`. Rewrite using `[monomial_mul, one_mul]`. Rewrite using `[hmm]`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, map_pow, map_neg, map_one]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq]`. Conclude with `hli2`.
-/
theorem restKey_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestKey C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hB
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have hN : segN X.F j - r + r = segN X.F j := Nat.sub_add_cancel hrN
  have h10 : BracketPolynomialSpan D := hAdm.2.2.2.2.2.2.2.2.2.1
  have h12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := (h12 p O S n' r K X.F X.L₁ X.N₁ j (fun _ => 0) (fun _ => 0) (fun _ => 0) hV hNK
    (fun _ => le_rfl)).2.1
  have hH : ∀ q : X.Idx p K j (X.restr j b),
      PlHyp (segN X.F j - r) (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) := by
    intro q
    obtain ⟨dd, hP, -⟩ := q.2
    exact plHyp_of X p K hX j _ _ dd hP
  have hpair : ∀ q : X.Idx p K j (X.restr j b), ∃ b' b'' : Fin (segN X.F j) → ℕ,
      (∃ P1 : PPath r (segN X.F j) (segLL X.F j) b', P1.mu = plPart q.1.1) ∧
      (∃ P2 : PPath K (segN X.F j) (segLL X.F j) b'', P2.mu = tanPart q.1.1) := by
    intro q
    obtain ⟨dd, hP, -⟩ := q.2
    obtain ⟨P, hPμ⟩ := hP.path
    obtain ⟨b', b'', -, h1, h2, -⟩ := (h10 (segN X.F j) r K (segLL X.F j) dd hNK (plPart q.1.1) (tanPart q.1.1)).mp
      ⟨P, by rw [hPμ, joinPT_parts]⟩
    exact ⟨b', b'', h1, h2⟩
  have hx : ∀ q : X.Idx p K j (X.restr j b),
      ((cutPath (segN X.F j - r) (plPart q.1.1), tanPart q.1.1) ∈ segPairsAll X.F j K) ∧
      IsSt (cutPath (segN X.F j - r) (plPart q.1.1)) (Icut (segN X.F j - r) (plPart q.1.1)) ∧
      IsSt (tanPart q.1.1) q.1.2.1 := by
    intro q
    obtain ⟨b', b'', ⟨P1, h1⟩, h2⟩ := hpair q
    obtain ⟨bc, Pc, hPc⟩ := cut_ppath P1 (segN X.F j - r)
    obtain ⟨dd, -, -, hSt, -⟩ := q.2
    exact ⟨⟨bc, b'', ⟨Pc, by rw [hPc, h1]⟩, h2⟩, isSt_cut hN (hH q), hSt⟩
  let x : X.Idx p K j (X.restr j b) →
      {x : ((Fin (segN X.F j + 1) → Fin r → ℤ) × (Fin (segN X.F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll X.F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} := fun q =>
    ⟨((cutPath (segN X.F j - r) (plPart q.1.1), tanPart q.1.1),
      (Icut (segN X.F j - r) (plPart q.1.1), q.1.2.1)), hx q⟩
  let M : X.Idx p K j (X.restr j b) → (ℤ × Fin (r + K) →₀ ℕ) := fun q =>
    X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)
  have htauI : ∀ m : Fin r, gp X K j (tauI (segN X.F j - r) hN m, m) ∈ tauSet X K j := by
    intro m
    have hm := m.isLt
    refine ⟨⟨r - 1 - m.val, by omega⟩, m, ?_⟩
    simp only [gp, Prod.mk.injEq, and_true]
    exact (segE_eq_fr_iff X.F hV j _ (by omega)).mpr rfl
  have hM : ∀ q, ∀ v, M q v ≠ 0 → v ∈ tauSet X K j := by
    intro q v hv
    by_contra hnot
    apply hv
    show (X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q.1.1)) v = 0
    rw [Finsupp.add_apply]
    have h1 : X.monTau K j q.1.2.2 v = 0 := by
      unfold Dat.monTau
      exact sum_single_apply_zero _ _ _ v fun i _ h => hnot ⟨i.1, i.2, h.symm⟩
    have h2 : dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) v = 0 := by
      unfold dgT
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      exact sum_single_apply_zero _ _ _ v fun m _ h => hnot (h ▸ htauI m)
    rw [h1, h2]
  have hsup : ∀ q, segRen X.F j O (r + K) (PsiPl O (x q).1.1.1 (x q).1.2.1 * PsiTan O (x q).1.1.2 (x q).1.2.2) ∈
      supported O (tauSet X K j)ᶜ := by
    intro q
    rw [map_mul, segRen_PsiPl, segRen_PsiTan]
    refine Subalgebra.mul_mem _ ?_ ?_
    · refine rename_mem_supported ?_ (Psi_cut_supported (segN X.F j - r) (by omega) (plPart q.1.1) _)
      rintro v hv ⟨t, c, h⟩
      simp only [gp, Prod.mk.injEq] at h
      have := (segE_eq_fr_iff X.F hV j v.1 t.isLt).mp h.1
      have hv' : v.1.val < segN X.F j - r := hv
      omega
    · refine rename_mem_supported (S := Set.univ) ?_ (by rw [supported_univ]; exact Algebra.mem_top)
      rintro v - ⟨t, c, h⟩
      simp only [gt, Prod.mk.injEq] at h
      exact castAdd_ne_natAdd K c v.2 h.2.symm
  have hinj : ∀ q q', M q = M q' → x q = x q' → q = q' := by
    intro q q' hMq hxq
    have hx' := congrArg Subtype.val hxq
    simp only [x, Prod.mk.injEq] at hx'
    obtain ⟨⟨hcut, hκ⟩, hI, hI''⟩ := hx'
    obtain ⟨b1, -, ⟨P1, h1⟩, -⟩ := hpair q
    obtain ⟨b2, -, ⟨P2, h2⟩, -⟩ := hpair q'
    have hν : plPart q.1.1 = plPart q'.1.1 :=
      path_eq_of_cut hN (hH q) (hH q') (fun i => by rw [← h1]; exact P1.dom i) (fun i => by rw [← h2]; exact P2.dom i)
        hcut hI
    have hμ : q.1.1 = q'.1.1 := by
      rw [← joinPT_parts q.1.1, ← joinPT_parts q'.1.1, hν, hκ]
    have hu0 : X.monTau K j q.1.2.2 = X.monTau K j q'.1.2.2 := by
      have h3 : X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q.1.1) =
          X.monTau K j q'.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q'.1.1) := hMq
      rw [hν] at h3
      exact add_right_cancel h3
    have hu : q.1.2.2 = q'.1.2.2 := by
      funext v
      rw [← monTau_apply X K hV j q.1.2.2 v.1 v.2, ← monTau_apply X K hV j q'.1.2.2 v.1 v.2, hu0]
    exact Subtype.ext (Prod.ext hμ (Prod.ext hI'' hu))
  have hli := li_mono_words (tauSet X K j) _ hw M x hM hsup hinj
  have hkill := fun q : X.Idx p K j (X.restr j b) =>
    kill_wordEl X K O hV j hN (X.beS p K j (X.restr j b) : ℤ) q.1 (hH q)
  choose e he using hkill
  have hli2 := hli.units_smul fun q => (-1 : Oˣ) ^ e q
  have heq : (fun q : X.Idx p K j (X.restr j b) =>
      monomial (X.monTau K j q.1.2.2) (1 : O) * kill (X.offSet K j) (X.wordEl K O j q.1)) =
      ((fun q => (-1 : Oˣ) ^ e q) • fun q => monomial (M q) (1 : O) *
        segRen X.F j O (r + K) (PsiPl O (x q).1.1.1 (x q).1.2.1 * PsiTan O (x q).1.1.2 (x q).1.2.2)) := by
    funext q
    rw [he q]
    simp only [Pi.smul_apply']
    rw [Units.smul_def, MvPolynomial.smul_eq_C_mul]
    have hmm : monomial (M q) (1 : O) = monomial (X.monTau K j q.1.2.2) (1 : O) *
        monomial (dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)) (1 : O) := by
      rw [monomial_mul, one_mul]
    rw [hmm]
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, map_pow, map_neg, map_one]
    ring
  rw [heq]
  exact hli2

end Formalism.MainNotions.SelectionLemmas.Pf
