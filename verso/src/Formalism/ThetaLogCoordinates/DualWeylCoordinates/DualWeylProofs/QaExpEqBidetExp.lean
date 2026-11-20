import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QaNuAntitone
import Formalism.GradedWeylDivisibility.FinalD

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qa_P (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    MvPolynomial (Fin n × Fin n) R :=
  ∏ c : ↥(TCols mu), initMinor R (qa_row I c) (colH_le mu c)

def qa_e {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin (Fintype.card ↥(TCols mu)) ≃ ↥(TCols mu) :=
  (Fintype.equivFin ↥(TCols mu)).symm

/- English proof (translation)
Unfold `qa_P bideterminant`. Conclude with `(Fintype.prod_equiv (qa_e mu) _ _ (fun _ => rfl)).symm`.
-/
lemma tableauBideterminant_eq_bideterminant (R : Type*) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_P R I = bideterminant R (fun k => colH mu (qa_e mu k)) (fun k => colH_le mu (qa_e mu k))
      (fun k => qa_row I (qa_e mu k)) := by
  unfold qa_P bideterminant
  exact (Fintype.prod_equiv (qa_e mu) _ _ (fun _ => rfl)).symm

/- English proof (translation)
Unfold `qa_exp bidetExp`. Conclude with `(Fintype.sum_equiv (qa_e mu) _ _ (fun _ => rfl)).symm`.
-/
lemma qa_exp_eq_bidetExp {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_exp I = bidetExp (fun k => colH mu (qa_e mu k)) (fun k => colH_le mu (qa_e mu k))
      (fun k => qa_row I (qa_e mu k)) := by
  unfold qa_exp bidetExp
  exact (Fintype.sum_equiv (qa_e mu) _ _ (fun _ => rfl)).symm

/- English proof (translation)
Unfold `colH`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`.

Establish `hsub : (Finset.univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t`. Introduce `m hm`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hm`. Rewrite using `[Finset.mem_Iio]`. Assume the negation of the conclusion as `hmt`.

Use `push_neg at hmt`. Use `hmu hmt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `absurd (lt_of_lt_of_le h ((Finset.card_le_card hsub).trans (Fin.card_Iio t).le)) (lt_irrefl _)`. Introduce `h`.

Establish `hsub : Finset.Iic t ⊆ (Finset.univ.filter fun m : Fin n => c ≤ mu m)`. Introduce `m hm`. Rewrite `hm` using `[Finset.mem_Iic]`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Conclude with `h.trans (hmu hm)`.

Conclude with `Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ((Fin.card_Iic t).symm.le.trans (Finset.card_le_card hsub))`.
-/
private theorem lt_colH_iff_le {n : ℕ} {mu : Fin n → ℤ} (hmu : Antitone mu) (c : ℤ) (t : Fin n) :
    (t : ℕ) < colH mu c ↔ c ≤ mu t := by
  unfold colH
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have hsub : (Finset.univ.filter fun m : Fin n => c ≤ mu m) ⊆ Finset.Iio t := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
      rw [Finset.mem_Iio]
      by_contra hmt
      push_neg at hmt
      have := hmu hmt
      omega
    exact absurd (lt_of_lt_of_le h ((Finset.card_le_card hsub).trans (Fin.card_Iio t).le)) (lt_irrefl _)
  · intro h
    have hsub : Finset.Iic t ⊆ (Finset.univ.filter fun m : Fin n => c ≤ mu m) := by
      intro m hm
      rw [Finset.mem_Iic] at hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.trans (hmu hm)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) ((Fin.card_Iic t).symm.le.trans (Finset.card_le_card hsub))

/- English proof (translation)
Establish `hmu' : Antitone mu` using `hmu`. Use function extensionality and compare the values at `t`. Unfold `shapeDeg qa_nu`. Establish `h1 : (Finset.univ.filter fun k => (t : ℕ) < colH mu ↑(qa_e mu k)).card = (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card` using `Finset.card_equiv (qa_e mu) (by simp)`. Establish `h2 : (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card = ((TCols mu).filter fun c => (t : ℕ) < colH mu c).card`.

Rewrite using `[Finset.card_filter, Finset.card_filter]`. Conclude with `Finset.sum_coe_sort (TCols mu) (fun c => if (t : ℕ) < colH mu c then 1 else 0)`. Establish `h3 : ((TCols mu).filter fun c => (t : ℕ) < colH mu c) = Finset.Ioc (mu (lastIdx n)) (mu t)`. Use extensionality with `c`. Establish `h0 : mu t ≤ mu 0` using `hmu' (by simp [Fin.le_iff_val_le_val])`.

Simplify using `only [TCols, Finset.mem_filter, Finset.mem_Ioc, lt_colH_iff_le hmu']`. Apply the tactic sequence `constructor <;> intro h <;> omega`. Conclude with `h1.trans (h2.trans (by rw [h3, Int.card_Ioc]))`.
-/
lemma qa_shape {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    shapeDeg (n := n) (fun k => colH mu (qa_e mu k)) = qa_nu mu := by
  have hmu' : Antitone mu := hmu
  funext t
  unfold shapeDeg qa_nu
  have h1 : (Finset.univ.filter fun k => (t : ℕ) < colH mu ↑(qa_e mu k)).card =
      (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card :=
    Finset.card_equiv (qa_e mu) (by simp)
  have h2 : (Finset.univ.filter fun c : ↥(TCols mu) => (t : ℕ) < colH mu ↑c).card =
      ((TCols mu).filter fun c => (t : ℕ) < colH mu c).card := by
    rw [Finset.card_filter, Finset.card_filter]
    exact Finset.sum_coe_sort (TCols mu) (fun c => if (t : ℕ) < colH mu c then 1 else 0)
  have h3 : ((TCols mu).filter fun c => (t : ℕ) < colH mu c) = Finset.Ioc (mu (lastIdx n)) (mu t) := by
    ext c
    have h0 : mu t ≤ mu 0 := hmu' (by simp [Fin.le_iff_val_le_val])
    simp only [TCols, Finset.mem_filter, Finset.mem_Ioc, lt_colH_iff_le hmu']
    constructor <;> intro h <;> omega
  exact h1.trans (h2.trans (by rw [h3, Int.card_Ioc]))

/- English proof (translation)
Rewrite using `[tableauBideterminant_eq_bideterminant, qa_exp_eq_bidetExp]`. Conclude with `column_lex_bideterminant R n n _ _ _ _ fun k => qa_row_strictMono I _`.
-/
lemma tableauBideterminant_degree_leadingCoeff (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    (colLex n n).degree (qa_P R I) = qa_exp I ∧ (colLex n n).leadingCoeff (qa_P R I) = 1 := by
  rw [tableauBideterminant_eq_bideterminant, qa_exp_eq_bidetExp]
  exact column_lex_bideterminant R n n _ _ _ _ fun k => qa_row_strictMono I _

/- English proof (translation)
Rewrite using `[tableauBideterminant_eq_bideterminant, ← qa_shape hmu]`. Conclude with `bidetMem R n n _ _ _ _`.
-/
lemma tableauBideterminant_mem_dualWeyl (R : Type) [CommRing R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    qa_P R I ∈ dualWeyl R n n (qa_nu mu) := by
  rw [tableauBideterminant_eq_bideterminant, ← qa_shape hmu]
  exact bidetMem R n n _ _ _ _

/- English proof (translation)
Introduce `h`. Use `(tableauBideterminant_degree_leadingCoeff R I).2` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.
-/
lemma tableauBideterminant_ne_zero (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) :
    qa_P R I ≠ 0 := by
  intro h
  have := (tableauBideterminant_degree_leadingCoeff R I).2
  rw [h] at this
  simp at this

/- English proof (translation)
Unfold `qa_P`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations. Unfold `initMinor`. Rewrite using `[RingHom.map_det]`.

Use `congr 1`. Use extensionality with `p q`. Simplify using the standard rewrite rules.
-/
lemma map_tableauBideterminant {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} [NeZero n] {mu : Fin n → ℤ}
    (I : TIdx mu) : MvPolynomial.map φ (qa_P R I) = qa_P S I := by
  unfold qa_P
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  unfold initMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp

/- English proof (translation)
Establish `h1` using `leadInterlaced ℤ n n (qa_nu mu) (qa_P ℤ I) (tableauBideterminant_mem_dualWeyl ℤ hmu I) (tableauBideterminant_ne_zero ℤ I)`. Establish `h2` using `colSums ℤ n n (qa_nu mu) (qa_P ℤ I) (tableauBideterminant_mem_dualWeyl ℤ hmu I) _ (((colLex n n).degree_mem_support_iff _).mpr (tableauBideterminant_ne_zero ℤ I))`. Rewrite `h1`, `h2` using `[(tableauBideterminant_degree_leadingCoeff ℤ I).1]`. Conclude with `⟨h1, h2⟩`.
-/
lemma qa_exp_mem {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    qa_exp I ∈ ssIdx n n (qa_nu mu) := by
  have h1 := leadInterlaced ℤ n n (qa_nu mu) (qa_P ℤ I) (tableauBideterminant_mem_dualWeyl ℤ hmu I) (tableauBideterminant_ne_zero ℤ I)
  have h2 := colSums ℤ n n (qa_nu mu) (qa_P ℤ I) (tableauBideterminant_mem_dualWeyl ℤ hmu I) _
    (((colLex n n).degree_mem_support_iff _).mpr (tableauBideterminant_ne_zero ℤ I))
  rw [(tableauBideterminant_degree_leadingCoeff ℤ I).1] at h1 h2
  exact ⟨h1, h2⟩

def qa_stdEquiv {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    {I : TIdx mu // StdT I} ≃ ssIdx n n (qa_nu mu) :=
  Equiv.ofBijective (fun I => ⟨qa_exp I.1, qa_exp_mem hmu I.1⟩)
    ⟨fun I J h => Subtype.ext (qa_exp_inj I.1 J.1 I.2 J.2 (congrArg Subtype.val h)),
     fun m => by
      obtain ⟨I, hI, he⟩ := qa_exp_surj hmu m.1 m.2
      exact ⟨⟨I, hI⟩, Subtype.ext he⟩⟩

/- English proof (translation)
Use `ldbasis_linearIndependent (colLex n n) _ ?_ fun I => (tableauBideterminant_degree_leadingCoeff R I.1).2` and prove the remaining obligations. Introduce `I J h`. Simplify using `only [(tableauBideterminant_degree_leadingCoeff R _).1] at h`. Conclude with `Subtype.ext (qa_exp_inj I.1 J.1 I.2 J.2 h)`.
-/
theorem linearIndependent_standard_tableauBideterminant (R : Type) [CommRing R] [Nontrivial R] {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :
    LinearIndependent R (fun I : {I : TIdx mu // StdT I} => qa_P R I.1) := by
  refine ldbasis_linearIndependent (colLex n n) _ ?_ fun I => (tableauBideterminant_degree_leadingCoeff R I.1).2
  intro I J h
  simp only [(tableauBideterminant_degree_leadingCoeff R _).1] at h
  exact Subtype.ext (qa_exp_inj I.1 J.1 I.2 J.2 h)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. It suffices to establish `key : ∀ d : (colLex n n).syn, ∀ f ∈ dualWeyl B n n (qa_nu mu), (colLex n n).toSyn ((colLex n n).degree f) = d → f ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) by`. Introduce `f hf`. Conclude with `key _ f hf rfl`. Introduce `d`.

Proceed by induction on `d using WellFoundedLT.induction with`. Consider the case `_ d ih`. Introduce `f hf hd`. Distinguish the cases in `hf0 : f = 0`. Rewrite using `[hf0]`.

Conclude with `Submodule.zero_mem _`. Establish `hint : Interlaced ((colLex n n).degree f)` using `leadInterlaced B n n _ f hf hf0`. Establish `hcol` using `colSums B n n _ f hf _ (((colLex n n).degree_mem_support_iff f).mpr hf0)`. Take `⟨I, hI, he⟩` from `qa_exp_surj hmu _ ⟨hint, hcol⟩`. Establish `hbS : qa_P B I ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1)` using `Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩`.

Establish `hdecomp : f = (f - (colLex n n).leadingCoeff f • qa_P B I) + (colLex n n).leadingCoeff f • qa_P B I`. Normalize the expressions using the abelian group laws. Rewrite using `[hdecomp]`. Use `Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hbS)` and prove the remaining obligations. Distinguish the cases in `h0 : f - (colLex n n).leadingCoeff f • qa_P B I = 0`.

Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`. Establish `hlt` using `lcassem_sub_lt (colLex n n) (f := f) (g := qa_P B I) ((tableauBideterminant_degree_leadingCoeff B I).1.trans he) (tableauBideterminant_degree_leadingCoeff B I).2 h0`. Conclude with `ih _ (hd ▸ hlt) _ (Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (tableauBideterminant_mem_dualWeyl B hmu I))) rfl`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨I, rfl⟩`. Conclude with `tableauBideterminant_mem_dualWeyl B hmu I.1`.
-/
theorem dualWeyl_eq_span_standard_tableauBideterminant (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) =
      Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) := by
  apply le_antisymm
  · suffices key : ∀ d : (colLex n n).syn, ∀ f ∈ dualWeyl B n n (qa_nu mu),
        (colLex n n).toSyn ((colLex n n).degree f) = d →
          f ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) by
      intro f hf
      exact key _ f hf rfl
    intro d
    induction d using WellFoundedLT.induction with
    | _ d ih =>
      intro f hf hd
      by_cases hf0 : f = 0
      · rw [hf0]; exact Submodule.zero_mem _
      have hint : Interlaced ((colLex n n).degree f) := leadInterlaced B n n _ f hf hf0
      have hcol := colSums B n n _ f hf _ (((colLex n n).degree_mem_support_iff f).mpr hf0)
      obtain ⟨I, hI, he⟩ := qa_exp_surj hmu _ ⟨hint, hcol⟩
      have hbS : qa_P B I ∈ Submodule.span B (Set.range fun I : {I : TIdx mu // StdT I} => qa_P B I.1) :=
        Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩
      have hdecomp : f = (f - (colLex n n).leadingCoeff f • qa_P B I) + (colLex n n).leadingCoeff f • qa_P B I := by
        abel
      rw [hdecomp]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hbS)
      by_cases h0 : f - (colLex n n).leadingCoeff f • qa_P B I = 0
      · rw [h0]; exact Submodule.zero_mem _
      have hlt := lcassem_sub_lt (colLex n n) (f := f) (g := qa_P B I) ((tableauBideterminant_degree_leadingCoeff B I).1.trans he)
        (tableauBideterminant_degree_leadingCoeff B I).2 h0
      exact ih _ (hd ▸ hlt) _ (Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (tableauBideterminant_mem_dualWeyl B hmu I))) rfl
  · rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact tableauBideterminant_mem_dualWeyl B hmu I.1

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[dualWeyl_eq_span_standard_tableauBideterminant B hmu]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨I, rfl⟩`. Conclude with `⟨I.1, rfl⟩`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨I, rfl⟩`. Conclude with `tableauBideterminant_mem_dualWeyl B hmu I`.
-/
theorem dualWeyl_eq_span_tableauBideterminant (B : Type) [CommRing B] [IsDomain B] {n : ℕ} [NeZero n] {mu : Fin n → ℤ}
    (hmu : Dominant mu) :
    dualWeyl B n n (qa_nu mu) = Submodule.span B (Set.range fun I : TIdx mu => qa_P B I) := by
  apply le_antisymm
  · rw [dualWeyl_eq_span_standard_tableauBideterminant B hmu]
    apply Submodule.span_mono
    rintro _ ⟨I, rfl⟩
    exact ⟨I.1, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨I, rfl⟩
    exact tableauBideterminant_mem_dualWeyl B hmu I

end Formalism.InvariantFactorPaths.ColumnFamilies
