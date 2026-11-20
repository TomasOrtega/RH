import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndEncPf
import Formalism.LocalToGlobal.ProjectiveLattices.IsExpChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.KillAdd

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

def colIdx {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    (m : LtN Dw n →₀ ℕ) : Fin n × Fin (dL Dw) →₀ ℕ :=
  Finsupp.mapDomain (fun p : LtN Dw n => (p.2.2, ltIdx Dw ⟨p.1, p.2.1⟩)) m

def mVal {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    {S : Type} [CommRing S] (G : MvPowerSeries (Fin n × Fin (dL Dw)) S) (m : LtN Dw n →₀ ℕ) : S :=
  (m.prod fun _ e => (e.factorial : S)) * MvPowerSeries.coeff (colIdx m) G

def KillAddValColSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (k n : ℕ)
    (G : MvPowerSeries (Fin n × Fin (dL Dw)) S) (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S),
    PsiCoverSt H →
    (∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1) →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n →
      ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          mVal (Germ.FB.expS S (-((k : S)) • TB.quadCol (n := n) β) * G) m =
        ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * mVal G m

namespace KAV

open MvPowerSeries

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro F N`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `F N`.

Rewrite using `[Function.iterate_succ_apply, ih, MvPowerSeries.coeff_pderiv, Finset.prod_range_succ]`. Establish `e1 : (N + k • Finsupp.single i 1 : σ →₀ ℕ) i = N i + k` using `by simp`. Establish `e2 : N + k • Finsupp.single i 1 + Finsupp.single i 1 = N + (k + 1) • Finsupp.single i 1`. Rewrite using `[add_smul, one_smul, add_assoc]`. Rewrite using `[e1, e2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_iterate_pderiv {σ R : Type} [CommRing R] (i : σ) (k : ℕ) :
    ∀ (F : MvPowerSeries σ R) (N : σ →₀ ℕ), coeff N ((pderiv R i)^[k] F) =
      (∏ t ∈ Finset.range k, ((N i + t + 1 : ℕ) : R)) * coeff (N + k • Finsupp.single i 1) F := by
  induction k with
  | zero => intro F N; simp
  | succ k ih =>
    intro F N
    rw [Function.iterate_succ_apply, ih, MvPowerSeries.coeff_pderiv, Finset.prod_range_succ]
    have e1 : (N + k • Finsupp.single i 1 : σ →₀ ℕ) i = N i + k := by simp
    have e2 : N + k • Finsupp.single i 1 + Finsupp.single i 1 = N + (k + 1) • Finsupp.single i 1 := by
      rw [add_smul, one_smul, add_assoc]
    rw [e1, e2]
    push_cast
    ring

/- English proof (translation)
The claim follows from `| [], _, _, N, _ => by simp | p :: L, hnd, hinj, N, hN => by rw [List.foldr_cons, coeff_iterate_pderiv, hN p (List.mem_cons_self ..), coeff_foldr φ m F L (List.nodup_cons.1 hnd).2 (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))] · rw [List.map_ …`.
-/
theorem coeff_foldr {σ κ R : Type} [CommRing R] (φ : κ → σ) (m : κ → ℕ) (F : MvPowerSeries σ R) :
    ∀ (L : List κ), L.Nodup → (∀ p ∈ L, ∀ q ∈ L, φ p = φ q → p = q) → ∀ N : σ →₀ ℕ, (∀ p ∈ L, N (φ p) = 0) →
      coeff N (L.foldr (fun p g => (pderiv R (φ p))^[m p] g) F) =
        (L.map fun p => ((m p).factorial : R)).prod * coeff (N + (L.map fun p => m p • Finsupp.single (φ p) 1).sum) F
  | [], _, _, N, _ => by simp
  | p :: L, hnd, hinj, N, hN => by
    rw [List.foldr_cons, coeff_iterate_pderiv, hN p (List.mem_cons_self ..), coeff_foldr φ m F L
      (List.nodup_cons.1 hnd).2 (fun a ha b hb => hinj a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))]
    · rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons]
      have hf : (∏ t ∈ Finset.range (m p), ((0 + t + 1 : ℕ) : R)) = ((m p).factorial : R) := by
        rw [← Finset.prod_range_add_one_eq_factorial]
        push_cast
        refine Finset.prod_congr rfl fun t _ => ?_
        ring
      rw [hf, add_assoc]
      ring
    · intro q hq
      have hpq : φ q ≠ φ p := fun h => (List.nodup_cons.1 hnd).1
        (hinj q (List.mem_cons_of_mem _ hq) p (List.mem_cons_self ..) h ▸ hq)
      simp [hN q (List.mem_cons_of_mem _ hq), hpq.symm]

/- English proof (translation)
Unfold `TB.dAdd`. Rewrite using `[Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `j' _ hj'`. Simplify using `[Pi.single_apply, hj']`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.
-/
theorem dAdd_single {S : Type} [CommRing S] {d n : ℕ} (j : Fin d) (b : Fin n) (G : Germ.PS S n d) :
    TB.dAdd (Pi.single j 1) b G = pderiv S (b, j) G := by
  unfold TB.dAdd
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    simp [Pi.single_apply, hj']
  · intro h
    exact absurd (Finset.mem_univ j) h

/- English proof (translation)
The claim follows from `funext fun G => dAdd_single j b G`.
-/
theorem dAdd_single' {S : Type} [CommRing S] {d n : ℕ} (j : Fin d) (b : Fin n) :
    (TB.dAdd (Pi.single j 1) b : Germ.PS S n d → Germ.PS S n d) = pderiv S (b, j) :=
  funext fun G => dAdd_single j b G

/- English proof (translation)
Unfold `TB.polyAdd`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, MvPowerSeries.constantCoeff_C]`. Use `congr 1`.

Simplify using `only [dAdd_single']`. Rewrite using `[← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_foldr (fun p : ι × Fin n => (p.2, e p.1)) m G _ (Finset.nodup_toList _) ?_ 0 (fun _ _ => by simp), zero_add, Finset.prod_map_toList, Finset.sum_map_toList]`. Introduce `p _ q _ h`. Simplify using `only [Prod.mk.injEq] at h`. Conclude with `Prod.ext (he h.2) h.1`.
-/
theorem constantCoeff_polyAdd {S : Type} [CommRing S] {d n : ℕ} {ι : Type} [Fintype ι] (e : ι → Fin d)
    (he : Function.Injective e) (P : MvPolynomial (ι × Fin n) S) (G : Germ.PS S n d) :
    constantCoeff (TB.polyAdd (fun l => Pi.single (e l) 1) P G) =
      ∑ m ∈ P.support, P.coeff m * ((∏ p, ((m p).factorial : S)) *
        coeff (∑ p, m p • Finsupp.single (p.2, e p.1) 1) G) := by
  classical
  unfold TB.polyAdd
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, MvPowerSeries.constantCoeff_C]
  congr 1
  simp only [dAdd_single']
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_foldr (fun p : ι × Fin n => (p.2, e p.1)) m G _ (Finset.nodup_toList _) ?_ 0 (fun _ _ => by simp),
    zero_add, Finset.prod_map_toList, Finset.sum_map_toList]
  intro p _ q _ h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext (he h.2) h.1

end KAV

namespace KAV

open MvPowerSeries

/- English proof (translation)
Establish `hinj : Function.Injective (ltEquiv Dw n)` using `(ltEquiv Dw n).injective`. Unfold `encP`. Rewrite using `[MvPolynomial.map_rename, MvPolynomial.support_rename_of_injective hinj, Finset.sum_image (fun x _ y _ h => Finsupp.mapDomain_injective hinj h)]`. Simplify using `only [MvPolynomial.coeff_rename_mapDomain _ hinj, MvPolynomial.coeff_map, Finsupp.equivMapDomain_eq_mapDomain]`. Use `Finset.sum_subset (MvPolynomial.support_map_subset _ _) ?_` and prove the remaining obligations.

Introduce `m _ hm`. Rewrite `hm` using `[MvPolynomial.notMem_support_iff, MvPolynomial.coeff_map]`. Rewrite using `[hm, zero_mul]`.
-/
theorem sum_encP {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    {K S : Type} [CommRing K] [CommRing S] (φ : K →+* S) (P : MvPolynomial (LtN Dw n) K)
    (V : ((Σ τ : E →+* ℂ, Fin (Dw.mult τ)) × Fin n →₀ ℕ) → S) :
    ∑ m' ∈ (MvPolynomial.map φ (encP P)).support, (MvPolynomial.map φ (encP P)).coeff m' * V m' =
      ∑ m ∈ P.support, φ (P.coeff m) * V (Finsupp.equivMapDomain (ltEquiv Dw n) m) := by
  classical
  have hinj : Function.Injective (ltEquiv Dw n) := (ltEquiv Dw n).injective
  unfold encP
  rw [MvPolynomial.map_rename, MvPolynomial.support_rename_of_injective hinj,
    Finset.sum_image (fun x _ y _ h => Finsupp.mapDomain_injective hinj h)]
  simp only [MvPolynomial.coeff_rename_mapDomain _ hinj, MvPolynomial.coeff_map,
    Finsupp.equivMapDomain_eq_mapDomain]
  refine Finset.sum_subset (MvPolynomial.support_map_subset _ _) ?_
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff, MvPolynomial.coeff_map] at hm
  rw [hm, zero_mul]

end KAV

namespace KAV

open MvPowerSeries

/- English proof (translation)
Unfold `mVal colIdx`. Use `congr 1`. Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => by simp)]`. Conclude with `Fintype.prod_equiv (ltEquiv Dw n).symm _ _ (fun p => by simp [Finsupp.equivMapDomain_apply])`. Use `congr 2`.

Rewrite using `[Finsupp.mapDomain, Finsupp.sum_fintype _ _ (fun _ => by simp)]`. Use `Fintype.sum_equiv (ltEquiv Dw n).symm _ _ (fun p => ?_)` and prove the remaining obligations. Apply the tactic sequence `rw [Finsupp.equivMapDomain_apply, Finsupp.smul_single_one] <;> rfl`.
-/
theorem val_encP {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {n : ℕ}
    {S : Type} [CommRing S] (G : MvPowerSeries (Fin n × Fin (dL Dw)) S) (m : LtN Dw n →₀ ℕ) :
    (∏ p, ((Finsupp.equivMapDomain (ltEquiv Dw n) m p).factorial : S)) *
        coeff (∑ p, Finsupp.equivMapDomain (ltEquiv Dw n) m p • Finsupp.single (p.2, ltIdx Dw p.1) 1) G =
      mVal G m := by
  classical
  unfold mVal colIdx
  congr 1
  · rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    exact Fintype.prod_equiv (ltEquiv Dw n).symm _ _ (fun p => by simp [Finsupp.equivMapDomain_apply])
  · congr 2
    rw [Finsupp.mapDomain, Finsupp.sum_fintype _ _ (fun _ => by simp)]
    refine Fintype.sum_equiv (ltEquiv Dw n).symm _ _ (fun p => ?_)
    rw [Finsupp.equivMapDomain_apply, Finsupp.smul_single_one] <;> rfl

/- English proof (translation)
The claim follows from `star_star φ`.
-/
theorem conj_conj {E : Type} [Field E] (φ : E →+* ℂ) :
    ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ := star_star φ

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial s a`. Simplify using `only [MvPolynomial.pderiv_monomial]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Both sides reduce to the same expression. Rewrite using `[tsub_right_comm]`. Use `congr 1`. Simplify using `[Finsupp.single_apply, hij, Ne.symm hij]`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
-/
theorem pderiv_comm {σ R : Type} [CommRing R] (i j : σ) (P : MvPolynomial σ R) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [MvPolynomial.pderiv_monomial]
    by_cases hij : i = j
    · subst hij
      rfl
    · rw [tsub_right_comm]
      congr 1
      simp [Finsupp.single_apply, hij, Ne.symm hij]
      ring
  | add p q hp hq => simp only [map_add, hp, hq]

/- English proof (translation)
Establish `hinj : Function.Injective (ltEquiv Dw n)` using `(ltEquiv Dw n).injective`. Establish `hgen : ∀ ℓ ℓ' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), InPsi H ℓ.1 → ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 → ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) (encP P)) = 0`. Introduce and unpack `⟨τ, i⟩ ⟨τ', i'⟩ hτ h`. Simplify using `only at h hτ`. Substitute `h` using the available equality.

Establish `key` using `CIndEncPf.colSum_zero c a n P hP τ hτ i i'`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Unfold `encP`. Rewrite using `[show ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)), b) = ltEquiv Dw n ⟨ComplexEmbedding.conjugate τ, i', b⟩ from rfl, MvPolynomial.pderiv_rename hinj, show ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)), b) = ltEquiv Dw n ⟨τ, i, b⟩ from rfl, MvPolynomial.pde …`.

Use `_ = 0 := by rw [← map_sum, key, map_zero]`. Break down `hPsi ℓ.1 with h1 | h1` into its components or cases. Conclude with `hgen ℓ ℓ' h1 hℓ`. Establish `h2` using `hgen ℓ' ℓ (by rw [hℓ]; exact h1) (by rw [hℓ, conj_conj])`. Rewrite using `[Finset.sum_congr rfl fun b _ => pderiv_comm (ℓ, b) (ℓ', b) (encP P)]`.

Conclude with `h2`.
-/
theorem colSum_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    (c : Coeff l) (hPsi : PsiCoverSt H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (hP : P ∈ harmA c a n) (ℓ ℓ' : Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (hℓ : ℓ'.1 = ComplexEmbedding.conjugate ℓ.1) :
    ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) (encP P)) = 0 := by
  classical
  have hinj : Function.Injective (ltEquiv Dw n) := (ltEquiv Dw n).injective
  have hgen : ∀ ℓ ℓ' : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), InPsi H ℓ.1 →
      ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 →
      ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) (encP P)) = 0 := by
    rintro ⟨τ, i⟩ ⟨τ', i'⟩ hτ h
    simp only at h hτ
    subst h
    have key := CIndEncPf.colSum_zero c a n P hP τ hτ i i'
    calc ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i⟩, b)
          (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i'⟩, b) (encP P))
        = ∑ b : Fin n, MvPolynomial.rename (ltEquiv Dw n) (MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
            (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P)) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          unfold encP
          rw [show ((⟨ComplexEmbedding.conjugate τ, i'⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)), b) =
              ltEquiv Dw n ⟨ComplexEmbedding.conjugate τ, i', b⟩ from rfl,
            MvPolynomial.pderiv_rename hinj,
            show ((⟨τ, i⟩ : Σ τ : E →+* ℂ, Fin (Dw.mult τ)), b) = ltEquiv Dw n ⟨τ, i, b⟩ from rfl,
            MvPolynomial.pderiv_rename hinj]
      _ = 0 := by rw [← map_sum, key, map_zero]
  rcases hPsi ℓ.1 with h1 | h1
  · exact hgen ℓ ℓ' h1 hℓ
  · have h2 := hgen ℓ' ℓ (by rw [hℓ]; exact h1) (by rw [hℓ, conj_conj])
    rw [Finset.sum_congr rfl fun b _ => pderiv_comm (ℓ, b) (ℓ', b) (encP P)]
    exact h2

/- English proof (translation)
Use `set Q := MvPolynomial.map (algebraMap c.F S) (encP P) with hQ`. Establish `hcol : ∀ ℓ ℓ' : Lt1 Dw, ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 → ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0`. Introduce `ℓ ℓ' h`. Simplify using `only [hQ, MvPolynomial.pderiv_map]`. Rewrite using `[← map_sum, colSum_conj c hPsi a n P hP ℓ ℓ' h, map_zero]`.

Establish `hcol' : ∀ ℓ ℓ' : Lt1 Dw, ℓ.1 = ComplexEmbedding.conjugate ℓ'.1 → ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0`. Introduce `ℓ ℓ' h`. Rewrite using `[Finset.sum_congr rfl fun b _ => pderiv_comm (ℓ, b) (ℓ', b) Q]`. Conclude with `hcol ℓ' ℓ h`. Establish `hdot : ∀ i j, dotProduct (Pi.single i 1) (β.mulVec (Pi.single j 1)) = β i j`.

Introduce `i j`. Simplify using `[dotProduct, Matrix.mulVec, Pi.single_apply]`. Unfold `TB.secondOrder`. Simplify using `only [hdot, Fintype.sum_prod_type, apply_ite MvPolynomial.C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Use `Finset.sum_eq_zero fun ℓ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun ℓ' _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, map_add, add_mul]`. Establish `h1 : MvPolynomial.C (β (ltIdx Dw ℓ) (ltIdx Dw ℓ')) * ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0`. Distinguish the cases in `hb : β (ltIdx Dw ℓ) (ltIdx Dw ℓ') = 0`.

Rewrite using `[hb, map_zero, zero_mul]`. Rewrite using `[hcol ℓ ℓ' (by simpa using hβ _ _ hb), mul_zero]`. Establish `h2 : MvPolynomial.C (β (ltIdx Dw ℓ') (ltIdx Dw ℓ)) * ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0`. Distinguish the cases in `hb : β (ltIdx Dw ℓ') (ltIdx Dw ℓ) = 0`. Rewrite using `[hb, map_zero, zero_mul]`.

Rewrite using `[hcol' ℓ ℓ' (by simpa using hβ _ _ hb), mul_zero]`. Rewrite using `[h1, h2, add_zero]`.
-/
theorem secondOrder_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (c : Coeff l) {S : Type} [CommRing S] [Algebra c.F S] (hPsi : PsiCoverSt H)
    (β : Matrix (Fin (dL Dw)) (Fin (dL Dw)) S)
    (hβ : ∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmA c a n) :
    TB.secondOrder S (fun p p' : Lt1 Dw × Fin n => if p.2 = p'.2 then
      dotProduct (Pi.single (ltIdx Dw p.1) 1) (β.mulVec (Pi.single (ltIdx Dw p'.1) 1)) +
      dotProduct (Pi.single (ltIdx Dw p'.1) 1) (β.mulVec (Pi.single (ltIdx Dw p.1) 1)) else 0)
      (MvPolynomial.map (algebraMap c.F S) (encP P)) = 0 := by
  classical
  set Q := MvPolynomial.map (algebraMap c.F S) (encP P) with hQ
  have hcol : ∀ ℓ ℓ' : Lt1 Dw, ℓ'.1 = ComplexEmbedding.conjugate ℓ.1 →
      ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0 := by
    intro ℓ ℓ' h
    simp only [hQ, MvPolynomial.pderiv_map]
    rw [← map_sum, colSum_conj c hPsi a n P hP ℓ ℓ' h, map_zero]
  have hcol' : ∀ ℓ ℓ' : Lt1 Dw, ℓ.1 = ComplexEmbedding.conjugate ℓ'.1 →
      ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0 := by
    intro ℓ ℓ' h
    rw [Finset.sum_congr rfl fun b _ => pderiv_comm (ℓ, b) (ℓ', b) Q]
    exact hcol ℓ' ℓ h
  have hdot : ∀ i j, dotProduct (Pi.single i 1) (β.mulVec (Pi.single j 1)) = β i j := by
    intro i j
    simp [dotProduct, Matrix.mulVec, Pi.single_apply]
  unfold TB.secondOrder
  simp only [hdot, Fintype.sum_prod_type, apply_ite MvPolynomial.C, map_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun ℓ' _ => ?_
  rw [← Finset.mul_sum, map_add, add_mul]
  have h1 : MvPolynomial.C (β (ltIdx Dw ℓ) (ltIdx Dw ℓ')) *
      ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0 := by
    by_cases hb : β (ltIdx Dw ℓ) (ltIdx Dw ℓ') = 0
    · rw [hb, map_zero, zero_mul]
    · rw [hcol ℓ ℓ' (by simpa using hβ _ _ hb), mul_zero]
  have h2 : MvPolynomial.C (β (ltIdx Dw ℓ') (ltIdx Dw ℓ)) *
      ∑ b : Fin n, MvPolynomial.pderiv (ℓ, b) (MvPolynomial.pderiv (ℓ', b) Q) = 0 := by
    by_cases hb : β (ltIdx Dw ℓ') (ltIdx Dw ℓ) = 0
    · rw [hb, map_zero, zero_mul]
    · rw [hcol' ℓ ℓ' (by simpa using hβ _ _ hb), mul_zero]
  rw [h1, h2, add_zero]

end KAV

/- English proof (translation)
Introduce `E _ _ _ H Dw l c S _ _ _ k n G β hPsi hβ a P hP`. Establish `hK` using `h S (dL Dw) n (Lt1 Dw) (fun ℓ => Pi.single (ltIdx Dw ℓ) 1) β (MvPolynomial.map (algebraMap c.F S) (encP P)) (KAV.secondOrder_zero c hPsi β hβ a n P hP) (-(k : S)) G`. Simplify using `only [KAV.constantCoeff_polyAdd (ltIdx Dw) (ltIdx Dw).injective, KAV.sum_encP, KAV.val_encP] at hK`. Conclude with `hK`.
-/
theorem killAddValCol_of (h : TB.KillAddSt) : KillAddValColSt := by
  intro E _ _ _ H Dw l c S _ _ _ k n G β hPsi hβ a P hP
  have hK := h S (dL Dw) n (Lt1 Dw) (fun ℓ => Pi.single (ltIdx Dw ℓ) 1) β
    (MvPolynomial.map (algebraMap c.F S) (encP P)) (KAV.secondOrder_zero c hPsi β hβ a n P hP) (-(k : S)) G
  simp only [KAV.constantCoeff_polyAdd (ltIdx Dw) (ltIdx Dw).injective, KAV.sum_encP, KAV.val_encP] at hK
  exact hK

namespace KAV

open MvPowerSeries

/- English proof (translation)
Introduce `p q h` and use `by simp only [Prod.mk.injEq] at h exact Prod.ext (Subsingleton.elim _ _) h.2`.
-/
theorem colEmb_inj {n d : ℕ} (b : Fin n) : Function.Injective (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) :=
  fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subsingleton.elim _ _) h.2

def colPart {n d : ℕ} (b : Fin n) (M : Fin n × Fin d →₀ ℕ) : Fin 1 × Fin d →₀ ℕ :=
  Finsupp.comapDomain (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) M (colEmb_inj b).injOn

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_rename]`. Rewrite using `[Finset.sum_eq_single x]`. Introduce `y hy hne`. It suffices to derive a contradiction. Simplify using `only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy`.

Conclude with `hne (Finsupp.mapDomain_injective hf hy)`. Introduce `h`. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Simplify using the standard rewrite rules.
-/
private theorem coeff_rename_mapDomain_lemma {σ τ R : Type} (f : σ → τ) [Filter.TendstoCofinite f]
    [CommSemiring R] (hf : Function.Injective f) (p : MvPowerSeries σ R) (x : σ →₀ ℕ) :
    coeff (Finsupp.mapDomain f x) (rename f p) = coeff x p := by
  classical
  rw [MvPowerSeries.coeff_rename]
  rw [Finset.sum_eq_single x]
  · intro y hy hne
    exfalso
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hy
    exact hne (Finsupp.mapDomain_injective hf hy)
  · intro h
    exfalso
    apply h
    simp

/- English proof (translation)
Set `ι : Fin n → Fin 1 × Fin d → Fin n × Fin d` to `fun b p => (b, p.2)`. Set `Mb : Fin n → (Fin n × Fin d →₀ ℕ)` to `fun b => Finsupp.mapDomain (ι b) (colPart b M)`. Establish `hMb : ∀ b q, Mb b q = if q.1 = b then M q else 0`. Introduce `b q`. Take `⟨b', j⟩` from `q`.

Distinguish the cases in `h : b' = b`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl]`. Use `show Finsupp.mapDomain (ι b') (colPart b' M) (ι b' (0, j)) = M (b', j)`. Rewrite using `[Finsupp.mapDomain_apply (colEmb_inj b')]`.

Simplify using `[colPart, Finsupp.comapDomain_apply, ι]`. Rewrite using `[if_neg h]`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨p, hp⟩`. Simplify using `only [ι, Prod.mk.injEq] at hp`.

Conclude with `h hp.1.symm`. Rewrite using `[MvPowerSeries.coeff_prod]`. Rewrite using `[Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm Mb)]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.coe_equivFunOnFinite_symm]`.

Conclude with `coeff_rename_mapDomain_lemma _ (colEmb_inj b) _ _`. Introduce `l hl hne`. Assume the negation of the conclusion as `hprod`. Apply `hne` to reduce the goal to its premises. Establish `hsupp : ∀ b q, q.1 ≠ b → l b q = 0`.

Introduce `b q hq`. Assume the negation of the conclusion as `hlq`. Apply `hprod` to reduce the goal to its premises. Use `Finset.prod_eq_zero (Finset.mem_univ b) ?_` and prove the remaining obligations. Apply `MvPowerSeries.coeff_rename_eq_zero` to reduce the goal to its premises.

Introduce and unpack `⟨x, hx⟩`. Apply `hlq` to reduce the goal to its premises. Rewrite using `[← hx]`. Apply `Finsupp.mapDomain_notin_range` to reduce the goal to its premises. Introduce and unpack `⟨p, hp⟩`.

Conclude with `hq (by rw [← hp])`. Establish `hsum` using `(Finset.mem_finsuppAntidiag.1 hl).1`. Use `Finsupp.ext fun b => Finsupp.ext fun q => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.coe_equivFunOnFinite_symm, hMb]`. Use `split_ifs with hqb`.

Establish `hq` using `congrArg (fun F : Fin n × Fin d →₀ ℕ => F q) hsum`. Simplify using `only [Finsupp.finset_sum_apply] at hq`. Rewrite using `[← hq, Finset.sum_eq_single b]`. Introduce `b' _ hb'`. Conclude with `hsupp b' q (by rw [hqb]; exact Ne.symm hb')`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ b) h`. Conclude with `hsupp b q hqb`. Introduce `h`. It suffices to derive a contradiction.

Apply `h` to reduce the goal to its premises. Rewrite using `[Finset.mem_finsuppAntidiag]`. Use `⟨?_, Finset.subset_univ _⟩` and prove the remaining obligations. Use extensionality with `q`. Rewrite using `[Finsupp.finset_sum_apply]`.

Simplify using `only [Finsupp.coe_equivFunOnFinite_symm, hMb]`. Simplify using the standard rewrite rules.
-/
theorem coeff_prod_cols {S : Type} [CommRing S] {n d : ℕ} (g : Fin n → MvPowerSeries (Fin 1 × Fin d) S)
    (M : Fin n × Fin d →₀ ℕ) :
    coeff M (∏ b, rename (fun p : Fin 1 × Fin d => ((b, p.2) : Fin n × Fin d)) (g b)) =
      ∏ b, coeff (colPart b M) (g b) := by
  classical
  let ι : Fin n → Fin 1 × Fin d → Fin n × Fin d := fun b p => (b, p.2)
  let Mb : Fin n → (Fin n × Fin d →₀ ℕ) := fun b => Finsupp.mapDomain (ι b) (colPart b M)
  have hMb : ∀ b q, Mb b q = if q.1 = b then M q else 0 := by
    intro b q
    obtain ⟨b', j⟩ := q
    by_cases h : b' = b
    · subst h
      rw [if_pos rfl]
      show Finsupp.mapDomain (ι b') (colPart b' M) (ι b' (0, j)) = M (b', j)
      rw [Finsupp.mapDomain_apply (colEmb_inj b')]
      simp [colPart, Finsupp.comapDomain_apply, ι]
    · rw [if_neg h]
      apply Finsupp.mapDomain_notin_range
      rintro ⟨p, hp⟩
      simp only [ι, Prod.mk.injEq] at hp
      exact h hp.1.symm
  rw [MvPowerSeries.coeff_prod]
  rw [Finset.sum_eq_single (Finsupp.equivFunOnFinite.symm Mb)]
  · refine Finset.prod_congr rfl fun b _ => ?_
    rw [Finsupp.coe_equivFunOnFinite_symm]
    exact coeff_rename_mapDomain_lemma _ (colEmb_inj b) _ _
  · intro l hl hne
    by_contra hprod
    apply hne

    have hsupp : ∀ b q, q.1 ≠ b → l b q = 0 := by
      intro b q hq
      by_contra hlq
      apply hprod
      refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
      apply MvPowerSeries.coeff_rename_eq_zero
      rintro ⟨x, hx⟩
      apply hlq
      rw [← hx]
      apply Finsupp.mapDomain_notin_range
      rintro ⟨p, hp⟩
      exact hq (by rw [← hp])
    have hsum := (Finset.mem_finsuppAntidiag.1 hl).1
    refine Finsupp.ext fun b => Finsupp.ext fun q => ?_
    rw [Finsupp.coe_equivFunOnFinite_symm, hMb]
    split_ifs with hqb
    · have hq := congrArg (fun F : Fin n × Fin d →₀ ℕ => F q) hsum
      simp only [Finsupp.finset_sum_apply] at hq
      rw [← hq, Finset.sum_eq_single b]
      · intro b' _ hb'
        exact hsupp b' q (by rw [hqb]; exact Ne.symm hb')
      · intro h; exact absurd (Finset.mem_univ b) h
    · exact hsupp b q hqb
  · intro h
    exfalso
    apply h
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, Finset.subset_univ _⟩
    ext q
    rw [Finsupp.finset_sum_apply]
    simp only [Finsupp.coe_equivFunOnFinite_symm, hMb]
    simp

end KAV

def ProdColSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (S : Type) [CommRing S]
    (n : ℕ) (g : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : LtN Dw n →₀ ℕ),
    mVal (∏ b, MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw))) (g b)) m =
      ∏ b, expVal (g b) (colOf m b)

/- English proof (translation)
Introduce `E _ _ _ H Dw S _ n g m`. Unfold `mVal expVal`. Rewrite using `[KAV.coeff_prod_cols, Finset.prod_mul_distrib]`. Establish `hcol : ∀ b ℓ, colOf m b ℓ = m ⟨ℓ.1, ℓ.2, b⟩` using `fun b ℓ => rfl`. Use `congr 1`.

Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => by simp)]`. Simplify using `only [fun b => Finsupp.prod_fintype (colOf m b) (fun _ e => (e.factorial : S)) (fun _ => by simp), hcol]`. Rewrite using `[Finset.prod_comm, ← Fintype.prod_prod_type']`. Conclude with `Fintype.prod_equiv (ltEquiv Dw n) _ _ (fun p => rfl)`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations.

Use `congr 2`. Establish `hκ : Function.Injective (fun p : LtN Dw n => (p.2.2, ltIdx Dw ⟨p.1, p.2.1⟩))`. Introduce `p q h`. Simplify using `only [Prod.mk.injEq] at h`. Apply `(ltEquiv Dw n).injective` to reduce the goal to its premises.

Use `show ((⟨p.1, p.2.1⟩ : Lt1 Dw), p.2.2) = ((⟨q.1, q.2.1⟩ : Lt1 Dw), q.2.2)`. Rewrite using `[(ltIdx Dw).injective h.2, h.1]`. Establish `hι : Function.Injective (fun ℓ : Lt1 Dw => ((0 : Fin 1), ltIdx Dw ℓ))`. Introduce `p q h`. Simplify using `only [Prod.mk.injEq] at h`.

Conclude with `(ltIdx Dw).injective h.2`. Use `Finsupp.ext fun ⟨z, j⟩ => ?_` and prove the remaining obligations. Use `set ℓ := (ltIdx Dw).symm j with hℓ`. Establish `e1 : ((z, j) : Fin 1 × Fin (dL Dw)) = ((0 : Fin 1), ltIdx Dw ℓ)`. Rewrite using `[hℓ, Equiv.apply_symm_apply, Subsingleton.elim z 0]`.

Rewrite using `[e1, Finsupp.mapDomain_apply hι]`. Unfold `KAV.colPart colIdx`. Rewrite using `[Finsupp.comapDomain_apply]`. Simplify using `only`. Rewrite using `[show ((b, ltIdx Dw ℓ) : Fin n × Fin (dL Dw)) = (fun p : LtN Dw n => (p.2.2, ltIdx Dw ⟨p.1, p.2.1⟩)) (⟨ℓ.1, ℓ.2, b⟩ : LtN Dw n) from rfl, Finsupp.mapDomain_apply hκ]`.

Both sides reduce to the same expression.
-/
theorem prodCol_holds : ProdColSt := by
  classical
  intro E _ _ _ H Dw S _ n g m
  unfold mVal expVal
  rw [KAV.coeff_prod_cols, Finset.prod_mul_distrib]
  have hcol : ∀ b ℓ, colOf m b ℓ = m ⟨ℓ.1, ℓ.2, b⟩ := fun b ℓ => rfl
  congr 1
  · rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
    simp only [fun b => Finsupp.prod_fintype (colOf m b) (fun _ e => (e.factorial : S)) (fun _ => by simp), hcol]
    rw [Finset.prod_comm, ← Fintype.prod_prod_type']
    exact Fintype.prod_equiv (ltEquiv Dw n) _ _ (fun p => rfl)
  · refine Finset.prod_congr rfl fun b _ => ?_
    congr 2
    have hκ : Function.Injective (fun p : LtN Dw n => (p.2.2, ltIdx Dw ⟨p.1, p.2.1⟩)) := by
      intro p q h
      simp only [Prod.mk.injEq] at h
      apply (ltEquiv Dw n).injective
      show ((⟨p.1, p.2.1⟩ : Lt1 Dw), p.2.2) = ((⟨q.1, q.2.1⟩ : Lt1 Dw), q.2.2)
      rw [(ltIdx Dw).injective h.2, h.1]
    have hι : Function.Injective (fun ℓ : Lt1 Dw => ((0 : Fin 1), ltIdx Dw ℓ)) := by
      intro p q h
      simp only [Prod.mk.injEq] at h
      exact (ltIdx Dw).injective h.2
    refine Finsupp.ext fun ⟨z, j⟩ => ?_
    set ℓ := (ltIdx Dw).symm j with hℓ
    have e1 : ((z, j) : Fin 1 × Fin (dL Dw)) = ((0 : Fin 1), ltIdx Dw ℓ) := by
      rw [hℓ, Equiv.apply_symm_apply, Subsingleton.elim z 0]
    rw [e1, Finsupp.mapDomain_apply hι]
    unfold KAV.colPart colIdx
    rw [Finsupp.comapDomain_apply]
    dsimp only
    rw [show ((b, ltIdx Dw ℓ) : Fin n × Fin (dL Dw)) =
        (fun p : LtN Dw n => (p.2.2, ltIdx Dw ⟨p.1, p.2.1⟩)) (⟨ℓ.1, ℓ.2, b⟩ : LtN Dw n) from rfl,
      Finsupp.mapDomain_apply hκ]
    rfl

end Formalism.MainNotions.ModuliIntegralCharts.H1
