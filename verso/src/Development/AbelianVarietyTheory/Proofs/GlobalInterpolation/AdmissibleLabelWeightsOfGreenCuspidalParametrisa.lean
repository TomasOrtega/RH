import Mathlib
import Formalism.LocalToGlobal.TieTwRecOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.JoinSISel
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LemmaLSeriesWeightsOfGreenCuspidalParametrisatio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumCentralIdempotentOfIrrCharacterEqSimpleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceHarishChandraInducedEqProductCharactersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBlocksOfCuspidalCharacterListStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLnStatement

noncomputable section

namespace GlobalTheory.Top.Lq

open CategoryTheory Polynomial GlobalTheory.GLq Formalism.IrreducibleCountingLemmas.TYPES UniqueFactorizationMonoid GlobalTheory.SerCmp
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Use `haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩`. Use `haveI : Finite (Polynomial.degreeLT (ZMod g) (d + 1)) := Finite.of_equiv _ (Polynomial.degreeLTEquiv (ZMod g) (d + 1)).symm.toEquiv`. Use `(Set.toFinite (Polynomial.degreeLT (ZMod g) (d + 1) : Set (ZMod g)[X])).subset fun P hP => ?_` and prove the remaining obligations. Establish `h` using `Polynomial.degree_eq_natDegree hP.1.ne_zero`. Rewrite using `[SetLike.mem_coe, Polynomial.mem_degreeLT, h, hP.2.2.2]`.

Conclude with `Nat.lt_succ_self d` after adjusting the coercions.
-/
theorem finite_primeLab (d : ℕ) : {P : (ZMod g)[X] | IsPrimeLab d P}.Finite := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  haveI : Finite (Polynomial.degreeLT (ZMod g) (d + 1)) :=
    Finite.of_equiv _ (Polynomial.degreeLTEquiv (ZMod g) (d + 1)).symm.toEquiv
  refine (Set.toFinite (Polynomial.degreeLT (ZMod g) (d + 1) : Set (ZMod g)[X])).subset fun P hP => ?_
  have h := Polynomial.degree_eq_natDegree hP.1.ne_zero
  rw [SetLike.mem_coe, Polynomial.mem_degreeLT, h, hP.2.2.2]
  exact_mod_cast Nat.lt_succ_self d

/- English proof (translation)
Use `haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩`. Use `haveI : Invertible (Fintype.card (GL (Fin d) (ZMod g)) : ℂ) := invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)`. Establish `h1` using `FDRep.char_orthonormal V W`. Establish `h2` using `FDRep.char_orthonormal V V`. Establish `e : W.character = V.character` using `(funext h).symm`.

Rewrite `h1` using `[e, h2, if_pos ⟨Iso.refl V⟩]`. Assume the negation of the conclusion as `hn`. Rewrite `h1` using `[if_neg hn]`. Conclude with `one_ne_zero h1`.
-/
theorem iso_of_char {d : ℕ} (V W : FDRep ℂ (GL (Fin d) (ZMod g))) [Simple V] [Simple W]
    (h : ∀ x, V.character x = W.character x) : Nonempty (V ≅ W) := by
  haveI : NeZero g := ⟨(Fact.out : g.Prime).ne_zero⟩
  haveI : Invertible (Fintype.card (GL (Fin d) (ZMod g)) : ℂ) := invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  have h1 := FDRep.char_orthonormal V W
  have h2 := FDRep.char_orthonormal V V
  have e : W.character = V.character := (funext h).symm
  rw [e, h2, if_pos ⟨Iso.refl V⟩] at h1
  by_contra hn
  rw [if_neg hn] at h1
  exact one_ne_zero h1

/- English proof (translation)
Take `⟨a, b, c, e⟩` from `O.lab_spec d V hd hs hc`. Conclude with `⟨a, b, Formalism.L2.NT.coeff_zero_ne_of_monic_irr a b c, e⟩`.
-/
theorem primeLab_lab {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) {d : ℕ} (V : FDRep ℂ (GL (Fin d) (ZMod g)))
    (hd : 1 ≤ d) (hs : Simple V) (hc : IsCuspidal (ZMod g) V) : IsPrimeLab d (O.lab d V) := by
  obtain ⟨a, b, c, e⟩ := O.lab_spec d V hd hs hc
  exact ⟨a, b, Formalism.L2.NT.coeff_zero_ne_of_monic_irr a b c, e⟩

/- English proof (translation)
Break down `Nat.eq_zero_or_pos d with h0 | hd` into its components or cases. Conclude with `⟨id, id, fun P hP => ⟨hP, rfl⟩, fun V h => by omega⟩`. Take `⟨τ, h1, h2, h3⟩` from `hG g L d hd`. Establish `hV : ∀ P : {P : (ZMod g)[X] // IsPrimeLab d P}, ∃ V : FDRep ℂ (GL (Fin d) (ZMod g)), Simple V ∧ IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = τ P.1 x` using `fun P => by`. Establish `hc` using `(h1 P.1 P.2).1.2.1`.

Take `⟨V, hs, hx⟩` from `hc.2.1`. Establish `e : (fun x => V.character x) = τ P.1` using `funext hx`. Conclude with `⟨V, hs, (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).1 (e ▸ hc), hx⟩`. Use `choose W hWs hWc hWx using hV`. Set `p : {P : (ZMod g)[X] // IsPrimeLab d P} → {P : (ZMod g)[X] // IsPrimeLab d P}` to `fun P => ⟨O.lab d (W P), primeLab_lab O _ hd (hWs P) (hWc P)⟩`.

Establish `hinj : Function.Injective p` using `fun P Q h => by`. Take `⟨i⟩` from `O.lab_inj d (W P) (W Q) hd (hWs P) (hWc P) (hWs Q) (hWc Q) (congrArg Subtype.val h)`. Use `Subtype.ext (h2 _ _ P.2 Q.2 (funext fun x => ?_))` and prove the remaining obligations. Rewrite using `[← hWx, ← hWx, FDRep.char_iso i]`. Use `haveI : Finite {P : (ZMod g)[X] // IsPrimeLab d P} := (finite_primeLab d).to_subtype`.

Set `e` to `Equiv.ofBijective p (Finite.injective_iff_bijective.1 hinj)`. Use `⟨fun P => if h : IsPrimeLab d P then (e.symm ⟨P, h⟩).1 else P, fun P => if h : IsPrimeLab d P then (e ⟨P, h⟩).1 else P, fun P hP => ?_, fun V _ hs hc => ?_⟩` and prove the remaining obligations. Simplify using `only [dif_pos hP]`. Use `⟨(e.symm ⟨P, hP⟩).2, ?_⟩` and prove the remaining obligations. Rewrite using `[dif_pos (e.symm ⟨P, hP⟩).2]`.

Simplify using the standard rewrite rules. Take `⟨P, hP, hχ⟩` from `h3 _ ((GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).2 hc) haveI := hs haveI := hWs ⟨P, hP⟩`. Establish `hi` using `iso_of_char V (W ⟨P, hP⟩) fun x => by rw [hWx]; exact congrFun hχ x`. Establish `hl : O.lab d V = O.lab d (W ⟨P, hP⟩)` using `O.lab_iso d _ _ hi`. Establish `hp` using `primeLab_lab O V hd hs hc`.

Establish `e1 : (⟨O.lab d V, hp⟩ : {P : (ZMod g)[X] // IsPrimeLab d P}) = e ⟨P, hP⟩` using `Subtype.ext hl`. Simplify using `only [dif_pos hp]`. Rewrite using `[e1, Equiv.symm_apply_apply, hχ]`. Conclude with `(h1 P hP).1`.
-/
theorem exists_perm_deg (hG : Green) (L : LabelDatum g) {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) (d : ℕ) :
    ∃ σ π : (ZMod g)[X] → (ZMod g)[X], (∀ P, IsPrimeLab d P → IsPrimeLab d (σ P) ∧ π (σ P) = P) ∧
      ∀ V : FDRep ℂ (GL (Fin d) (ZMod g)), 1 ≤ d → Simple V → IsCuspidal (ZMod g) V →
        IsCuspOf L (σ (O.lab d V)) (fun x => V.character x) := by
  rcases Nat.eq_zero_or_pos d with h0 | hd
  · exact ⟨id, id, fun P hP => ⟨hP, rfl⟩, fun V h => by omega⟩
  obtain ⟨τ, h1, h2, h3⟩ := hG g L d hd
  have hV : ∀ P : {P : (ZMod g)[X] // IsPrimeLab d P}, ∃ V : FDRep ℂ (GL (Fin d) (ZMod g)), Simple V ∧
      IsCuspidal (ZMod g) V ∧ ∀ x, V.character x = τ P.1 x := fun P => by
    have hc := (h1 P.1 P.2).1.2.1
    obtain ⟨V, hs, hx⟩ := hc.2.1
    have e : (fun x => V.character x) = τ P.1 := funext hx
    exact ⟨V, hs, (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).1 (e ▸ hc), hx⟩
  choose W hWs hWc hWx using hV
  let p : {P : (ZMod g)[X] // IsPrimeLab d P} → {P : (ZMod g)[X] // IsPrimeLab d P} :=
    fun P => ⟨O.lab d (W P), primeLab_lab O _ hd (hWs P) (hWc P)⟩
  have hinj : Function.Injective p := fun P Q h => by
    obtain ⟨i⟩ := O.lab_inj d (W P) (W Q) hd (hWs P) (hWc P) (hWs Q) (hWc Q) (congrArg Subtype.val h)
    refine Subtype.ext (h2 _ _ P.2 Q.2 (funext fun x => ?_))
    rw [← hWx, ← hWx, FDRep.char_iso i]
  haveI : Finite {P : (ZMod g)[X] // IsPrimeLab d P} := (finite_primeLab d).to_subtype
  let e := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hinj)
  refine ⟨fun P => if h : IsPrimeLab d P then (e.symm ⟨P, h⟩).1 else P,
    fun P => if h : IsPrimeLab d P then (e ⟨P, h⟩).1 else P, fun P hP => ?_, fun V _ hs hc => ?_⟩
  · simp only [dif_pos hP]
    refine ⟨(e.symm ⟨P, hP⟩).2, ?_⟩
    rw [dif_pos (e.symm ⟨P, hP⟩).2]
    simp
  · obtain ⟨P, hP, hχ⟩ := h3 _ ((GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g d V hd hs).2 hc)
    haveI := hs
    haveI := hWs ⟨P, hP⟩
    have hi := iso_of_char V (W ⟨P, hP⟩) fun x => by rw [hWx]; exact congrFun hχ x
    have hl : O.lab d V = O.lab d (W ⟨P, hP⟩) := O.lab_iso d _ _ hi
    have hp := primeLab_lab O V hd hs hc
    have e1 : (⟨O.lab d V, hp⟩ : {P : (ZMod g)[X] // IsPrimeLab d P}) = e ⟨P, hP⟩ := Subtype.ext hl
    simp only [dif_pos hp]
    rw [e1, Equiv.symm_apply_apply, hχ]
    exact (h1 P hP).1

/- English proof (translation)
Use `choose σ π h1 h2 using exists_perm_deg hG L O`. Use `⟨fun P => σ P.natDegree P, fun P => π P.natDegree P, fun d P hP => ?_, fun d V hd hs hc => ?_⟩` and prove the remaining obligations. Establish `e` using `hP.2.2.2`. Establish `a` using `h1 d P hP`. Simplify using `only [e, a.1.2.2.2]`.

Conclude with `a`. Simplify using `only [(primeLab_lab O V hd hs hc).2.2.2]`. Conclude with `h2 d V hd hs hc`.
-/
theorem exists_perm (hG : Green) (L : LabelDatum g) {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) :
    ∃ σ π : (ZMod g)[X] → (ZMod g)[X], (∀ d P, IsPrimeLab d P → IsPrimeLab d (σ P) ∧ π (σ P) = P) ∧
      ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → Simple V → IsCuspidal (ZMod g) V →
        IsCuspOf L (σ (O.lab d V)) (fun x => V.character x) := by
  choose σ π h1 h2 using exists_perm_deg hG L O
  refine ⟨fun P => σ P.natDegree P, fun P => π P.natDegree P, fun d P hP => ?_, fun d V hd hs hc => ?_⟩
  · have e := hP.2.2.2
    have a := h1 d P hP
    simp only [e, a.1.2.2.2]
    exact a
  · simp only [(primeLab_lab O V hd hs hc).2.2.2]
    exact h2 d V hd hs hc

/- English proof (translation)
Rewrite using `[normalizedFactors_prod_eq M fun P hP => (h P hP).choose_spec.2.1]`. Use `conv_rhs => rw [← Multiset.map_id M]`. Conclude with `Multiset.map_congr rfl fun P hP => (h P hP).choose_spec.1.normalize_eq_self`.
-/
theorem nf_prod (M : Multiset (ZMod g)[X]) (h : ∀ P ∈ M, ∃ d, IsPrimeLab d P) : normalizedFactors M.prod = M := by
  rw [normalizedFactors_prod_eq M fun P hP => (h P hP).choose_spec.2.1]
  conv_rhs => rw [← Multiset.map_id M]
  exact Multiset.map_congr rfl fun P hP => (h P hP).choose_spec.1.normalize_eq_self

/- English proof (translation)
Use `⟨fun P hP => ?_, ?_⟩` and prove the remaining obligations. Take `⟨a, b, c, hc⟩` from `(Polynomial.mem_normalizedFactors_iff hm.ne_zero).1 hP`. Use `⟨b, a, fun h => h0 ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hc, mul_coeff_zero, h, zero_mul]`. Use `Polynomial.leadingCoeff_mul_prod_normalizedFactors f` as an intermediate fact.

Rewrite `this` using `[hm.leadingCoeff, C_1, one_mul]`. Then use the resulting hypothesis.
-/
theorem nf_lab {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    (∀ P ∈ normalizedFactors f, IsPrimeLab P.natDegree P) ∧ (normalizedFactors f).prod = f := by
  refine ⟨fun P hP => ?_, ?_⟩
  · obtain ⟨a, b, c, hc⟩ := (Polynomial.mem_normalizedFactors_iff hm.ne_zero).1 hP
    refine ⟨b, a, fun h => h0 ?_, rfl⟩
    rw [hc, mul_coeff_zero, h, zero_mul]
  · have := Polynomial.leadingCoeff_mul_prod_normalizedFactors f
    rwa [hm.leadingCoeff, C_1, one_mul] at this

def ext (σ : (ZMod g)[X] → (ZMod g)[X]) (f : (ZMod g)[X]) : (ZMod g)[X] := ((normalizedFactors f).map σ).prod

section Ext

variable {σ π : (ZMod g)[X] → (ZMod g)[X]} (hσ : ∀ d P, IsPrimeLab d P → IsPrimeLab d (σ P) ∧ π (σ P) = P)
include hσ

/- English proof (translation)
The claim follows from `nf_prod _ fun P hP => by obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.1 hP exact ⟨_, (hσ _ _ ((nf_lab hm h0).1 Q hQ)).1⟩`.
-/
theorem nf_ext {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    normalizedFactors (ext σ f) = (normalizedFactors f).map σ :=
  nf_prod _ fun P hP => by
    obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.1 hP
    exact ⟨_, (hσ _ _ ((nf_lab hm h0).1 Q hQ)).1⟩

/- English proof (translation)
Rewrite using `[ext, nf_ext hσ hm h0, Multiset.map_map]`. Use `conv_rhs => rw [← (nf_lab hm h0).2, ← Multiset.map_id (normalizedFactors f)]`. Use `congr 1`. Conclude with `Multiset.map_congr rfl fun P hP => (hσ _ _ ((nf_lab hm h0).1 P hP)).2`.
-/
theorem ext_back {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) : ext π (ext σ f) = f := by
  rw [ext, nf_ext hσ hm h0, Multiset.map_map]
  conv_rhs => rw [← (nf_lab hm h0).2, ← Multiset.map_id (normalizedFactors f)]
  congr 1
  exact Multiset.map_congr rfl fun P hP => (hσ _ _ ((nf_lab hm h0).1 P hP)).2

/- English proof (translation)
Establish `hP` using `(nf_lab hm h0).1`. Establish `hM : (ext σ f).Monic` using `monic_multiset_prod_of_monic _ _ fun P h => (hσ _ _ (hP P h)).1.1`. Use `⟨hM, ?_, ?_, fun hs => ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← (nf_lab hm h0).2]`. Rewrite using `[ext, natDegree_multiset_prod_of_monic _ fun P h => by`.

Take `⟨Q, hQ, rfl⟩` from `Multiset.mem_map.1 h`. Conclude with `(hσ _ _ (hP Q hQ)).1.1,`. Use `natDegree_multiset_prod_of_monic _ fun P h => (hP P h).1, Multiset.map_map]`. Use `congr 1`. Conclude with `Multiset.map_congr rfl fun P h => (hσ _ _ (hP P h)).1.2.2.2`.

Rewrite using `[ext, coeff_zero_multiset_prod]`. Use `Multiset.prod_ne_zero fun h => ?_` and prove the remaining obligations. Rewrite `h` using `[Multiset.map_map]`. Take `⟨Q, hQ, e⟩` from `Multiset.mem_map.1 h`. Conclude with `(hσ _ _ (hP Q hQ)).1.2.2.1 e`.

Rewrite using `[squarefree_iff_nodup_normalizedFactors hM.ne_zero, nf_ext hσ hm h0]`. Use `Multiset.Nodup.map_on (fun P h Q h' e => ?_) ((squarefree_iff_nodup_normalizedFactors hm.ne_zero).1 hs)` and prove the remaining obligations. Rewrite using `[← (hσ _ _ (hP P h)).2, e, (hσ _ _ (hP Q h')).2]`.
-/
theorem ext_lab {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    (ext σ f).Monic ∧ (ext σ f).natDegree = f.natDegree ∧ (ext σ f).coeff 0 ≠ 0 ∧ (Squarefree f → Squarefree (ext σ f)) := by
  have hP := (nf_lab hm h0).1
  have hM : (ext σ f).Monic := monic_multiset_prod_of_monic _ _ fun P h => (hσ _ _ (hP P h)).1.1
  refine ⟨hM, ?_, ?_, fun hs => ?_⟩
  · conv_rhs => rw [← (nf_lab hm h0).2]
    rw [ext, natDegree_multiset_prod_of_monic _ fun P h => by
        obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.1 h
        exact (hσ _ _ (hP Q hQ)).1.1,
      natDegree_multiset_prod_of_monic _ fun P h => (hP P h).1, Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun P h => (hσ _ _ (hP P h)).1.2.2.2
  · rw [ext, coeff_zero_multiset_prod]
    refine Multiset.prod_ne_zero fun h => ?_
    rw [Multiset.map_map] at h
    obtain ⟨Q, hQ, e⟩ := Multiset.mem_map.1 h
    exact (hσ _ _ (hP Q hQ)).1.2.2.1 e
  · rw [squarefree_iff_nodup_normalizedFactors hM.ne_zero, nf_ext hσ hm h0]
    refine Multiset.Nodup.map_on (fun P h Q h' e => ?_) ((squarefree_iff_nodup_normalizedFactors hm.ne_zero).1 hs)
    rw [← (hσ _ _ (hP P h)).2, e, (hσ _ _ (hP Q h')).2]

end Ext

/- English proof (translation)
Rewrite using `[ext, ← Multiset.prod_coe, nf_prod _ fun P hP => h P (Multiset.mem_coe.1 hP), Multiset.map_coe, Multiset.prod_coe]`.
-/
theorem ext_list (σ : (ZMod g)[X] → (ZMod g)[X]) (M : List (ZMod g)[X]) (h : ∀ P ∈ M, ∃ d, IsPrimeLab d P) :
    ext σ M.prod = (M.map σ).prod := by
  rw [ext, ← Multiset.prod_coe, nf_prod _ fun P hP => h P (Multiset.mem_coe.1 hP), Multiset.map_coe, Multiset.prod_coe]

section Dict

variable (L : LabelDatum g) {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) {σ π : (ZMod g)[X] → (ZMod g)[X]}
  (hσ : ∀ d P, IsPrimeLab d P → IsPrimeLab d (σ P) ∧ π (σ P) = P)
  (h1 : ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → Simple V → IsCuspidal (ZMod g) V →
        IsCuspOf L (σ (O.lab d V)) (fun x => V.character x))
include h1

/- English proof (translation)
Take `⟨s, b, lam, hb, hl, hcon, rfl⟩` from `hL`. Establish `hc : ∀ c, 1 ≤ Fintype.card {i // b i = c}` using `fun c => by`. Take `⟨i, hi⟩` from `hb c`. Conclude with `Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩`. Set `Q : List ((ZMod g)[X] × Pc g)` to `(List.finRange s).map fun c => (σ (labO O (lam c)), ⟨Fintype.card {i // b i = c}, fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩)`.

Establish `hQ : Q.map Prod.snd = canonList b lam`. Simplify using `only [Q, canonList, List.map_map]`. Both sides reduce to the same expression. Use `⟨Q, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`.

Simplify using `only [Q, List.mem_map] at hp`. Take `⟨c, -, rfl⟩` from `hp`. Conclude with `h1 _ _ (hc c) (Formalism.L2.PT.simple_transp _ (hl c).1) (Formalism.L2.PT.isCuspidal_transp _ (hl c).2)`. Rewrite using `[hQ]`. Unfold `degL canonList`.

Rewrite using `[List.map_map]`. Establish `e : ((List.finRange s).map ((fun p : Pc g => p.1) ∘ fun c : Fin s => (⟨Fintype.card {i // b i = c}, fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ : Pc g))).sum = ∑ c : Fin s, Fintype.card {i // b i = c}`. Rewrite using `[Fin.sum_univ_def]`. Both sides reduce to the same expression. Rewrite using `[e, ← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv b), Fintype.card_fin]`.

Rewrite using `[Fin.prod_univ_def, ext_list σ _ fun P hP => by`. Take `⟨c, -, rfl⟩` from `List.mem_map.1 hP`. Conclude with `⟨_, primeLab_lab O _ (hc c) (Formalism.L2.PT.simple_transp _ (hl c).1) (Formalism.L2.PT.isCuspidal_transp _ (hl c).2)⟩]`. Simplify using `only [Q, List.map_map]`. Both sides reduce to the same expression.

Rewrite using `[hQ]`. Establish `ht : (fun x => LinearMap.trace ℂ (hcSpace (ZMod g) b lam) (hcRep (ZMod g) b lam x)) = hcL (canonList b lam) r` using `funext (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g r s b lam hb)`. Use `(GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g r s b lam τ hτ).1 hcon` as an intermediate fact. Rewrite `this` using `[ht]`. Conclude with `this`.
-/
theorem hasLabel_of {r : ℕ} (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]) (hτ : Simple τ) (hL : HasLabelO O τ f) :
    HasLabel L (fun x => τ.character x) (ext σ f) := by
  obtain ⟨s, b, lam, hb, hl, hcon, rfl⟩ := hL
  have hc : ∀ c, 1 ≤ Fintype.card {i // b i = c} := fun c => by
    obtain ⟨i, hi⟩ := hb c
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  let Q : List ((ZMod g)[X] × Pc g) := (List.finRange s).map fun c =>
    (σ (labO O (lam c)), ⟨Fintype.card {i // b i = c},
      fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩)
  have hQ : Q.map Prod.snd = canonList b lam := by
    simp only [Q, canonList, List.map_map]
    rfl
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro p hp
    simp only [Q, List.mem_map] at hp
    obtain ⟨c, -, rfl⟩ := hp
    exact h1 _ _ (hc c) (Formalism.L2.PT.simple_transp _ (hl c).1) (Formalism.L2.PT.isCuspidal_transp _ (hl c).2)
  · rw [hQ]
    unfold degL canonList
    rw [List.map_map]
    have e : ((List.finRange s).map ((fun p : Pc g => p.1) ∘ fun c : Fin s =>
        (⟨Fintype.card {i // b i = c},
          fun x => (transp (Fintype.equivFin {i // b i = c}) (lam c)).character x⟩ : Pc g))).sum =
        ∑ c : Fin s, Fintype.card {i // b i = c} := by
      rw [Fin.sum_univ_def]
      rfl
    rw [e, ← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv b), Fintype.card_fin]
  · rw [Fin.prod_univ_def, ext_list σ _ fun P hP => by
      obtain ⟨c, -, rfl⟩ := List.mem_map.1 hP
      exact ⟨_, primeLab_lab O _ (hc c) (Formalism.L2.PT.simple_transp _ (hl c).1) (Formalism.L2.PT.isCuspidal_transp _ (hl c).2)⟩]
    simp only [Q, List.map_map]
    rfl
  · rw [hQ]
    have ht : (fun x => LinearMap.trace ℂ (hcSpace (ZMod g) b lam) (hcRep (ZMod g) b lam x)) =
        hcL (canonList b lam) r := funext (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g r s b lam hb)
    have := (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g r s b lam τ hτ).1 hcon
    rw [ht] at this
    exact this

omit h1 in
/- English proof (translation)
Take `⟨Q', hQ, hdeg, hf, hip⟩` from `hl`. Substitute `hdeg` using the available equality. Take `⟨b, lam, hb, hlam, hcan⟩` from `GlobalTheory.T.exists_blocks_of_cuspidal_character_list g (Q'.map Prod.snd) (by`. Introduce `p hp`. Take `⟨p', hp', rfl⟩` from `List.mem_map.1 hp`.

Establish `hχ` using `(hQ p' hp').2.1`. Take `⟨V, hV, hVχ⟩` from `hχ.2.1`. Establish `hχV : (fun x => V.character x) = p'.2.2` using `funext hVχ`. Conclude with `⟨hχ.1, V, hV, (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g _ V hχ.1 hV).1 (hχV ▸ hχ), hVχ⟩)`. Establish `hp : ∀ c, IsPrimeLab _ (labO O (lam c))` using `fun c => primeLab_lab O _ (by obtain ⟨i, hi⟩ := hb c; exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩) (Formalism.L2.PT.simple_transp _ (hlam c).1) (Formalism.L2.PT.isCuspidal_transp _ (hlam c).2)`.

Use `⟨∏ c, labO O (lam c), monic_prod_of_monic _ _ fun c _ => (hp c).1, ?_, _, b, lam, hb, hlam, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[coeff_zero_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 fun c _ => (hp c).2.2.1`. Use `(GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g _ _ b lam τ hτ).2 ?_` and prove the remaining obligations. Establish `e` using `funext (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g _ _ b lam hb)`.

Rewrite using `[e, hcan]`. Conclude with `hip`.
-/
theorem exists_labelO {r : ℕ} (τ : FDRep ℂ (GL (Fin r) (ZMod g))) (f : (ZMod g)[X]) (hτ : Simple τ)
    (hl : HasLabel L (fun x => τ.character x) f) : ∃ f', f'.Monic ∧ f'.coeff 0 ≠ 0 ∧ HasLabelO O τ f' := by
  obtain ⟨Q', hQ, hdeg, hf, hip⟩ := hl
  subst hdeg
  obtain ⟨b, lam, hb, hlam, hcan⟩ := GlobalTheory.T.exists_blocks_of_cuspidal_character_list g (Q'.map Prod.snd) (by
    intro p hp
    obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hp
    have hχ := (hQ p' hp').2.1
    obtain ⟨V, hV, hVχ⟩ := hχ.2.1
    have hχV : (fun x => V.character x) = p'.2.2 := funext hVχ
    exact ⟨hχ.1, V, hV, (GlobalTheory.T.isCuspidalCharacter_iff_isCuspidal_GLnFiniteField g _ V hχ.1 hV).1 (hχV ▸ hχ), hVχ⟩)
  have hp : ∀ c, IsPrimeLab _ (labO O (lam c)) := fun c =>
    primeLab_lab O _ (by obtain ⟨i, hi⟩ := hb c; exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩)
      (Formalism.L2.PT.simple_transp _ (hlam c).1) (Formalism.L2.PT.isCuspidal_transp _ (hlam c).2)
  refine ⟨∏ c, labO O (lam c), monic_prod_of_monic _ _ fun c _ => (hp c).1, ?_, _, b, lam, hb, hlam, ?_, rfl⟩
  · rw [coeff_zero_prod]
    exact Finset.prod_ne_zero_iff.2 fun c _ => (hp c).2.2.1
  · refine (GlobalTheory.T.isConstituent_harishChandraRep_iff_pairing_ne_zero g _ _ b lam τ hτ).2 ?_
    have e := funext (GlobalTheory.T.trace_harishChandra_induced_eq_product_characters g _ _ b lam hb)
    rw [e, hcan]
    exact hip

include hσ in
/- English proof (translation)
Establish `hB : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ → (HasLabel L (fun x => τ.character x) (ext σ f) ↔ HasLabelO O τ f)` using `fun τ hτ => by`. Use `⟨fun h => ?_, hasLabel_of L O h1 τ f hτ⟩` and prove the remaining obligations. Take `⟨f', a, b, c⟩` from `exists_labelO L O τ _ hτ h`. Establish `e` using `((GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L h5 hG r).1 _ ⟨τ, hτ, fun _ => rfl⟩).unique h (hasLabel_of L O h1 τ f' hτ c)`. Establish `e' : f = f'` using `by rw [← ext_back hσ hm h0, e, ext_back hσ a b]`.

Conclude with `e' ▸ c`. Unfold `eSerC Formalism.L2.NT.eSerO`. Rewrite using `[GlobalTheory.T.finsum_centralIdempotentOfIrrCharacter_eq_simple]`. Use `finsum_congr fun z => finsum_congr_Prop (propext ?_) fun _ => rfl` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨τ, hτ, hz, hl⟩`. Conclude with `⟨τ, hτ, hz, (hB τ hτ).2 hl⟩`. Introduce and unpack `⟨τ, hτ, hz, hl⟩`. Conclude with `⟨τ, hτ, hz, (hB τ hτ).1 hl⟩`.
-/
theorem eSer_eq (h5 : 5 ≤ g) (hG : Green) (r : ℕ) {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    Formalism.L2.NT.eSerO O r f = eSerC L r (ext σ f) := by
  have hB : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ →
      (HasLabel L (fun x => τ.character x) (ext σ f) ↔ HasLabelO O τ f) := fun τ hτ => by
    refine ⟨fun h => ?_, hasLabel_of L O h1 τ f hτ⟩
    obtain ⟨f', a, b, c⟩ := exists_labelO L O τ _ hτ h
    have e := ((GlobalTheory.T.harishChandraSeriesLabel_exists_unique_GLn g L h5 hG r).1 _ ⟨τ, hτ, fun _ => rfl⟩).unique h (hasLabel_of L O h1 τ f' hτ c)
    have e' : f = f' := by rw [← ext_back hσ hm h0, e, ext_back hσ a b]
    exact e' ▸ c
  unfold eSerC Formalism.L2.NT.eSerO
  rw [GlobalTheory.T.finsum_centralIdempotentOfIrrCharacter_eq_simple]
  refine finsum_congr fun z => finsum_congr_Prop (propext ?_) fun _ => rfl
  constructor
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).2 hl⟩
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).1 hl⟩

end Dict

open Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders in

/- English proof (translation)
Introduce `hG D jE T k ψ hψ`. Use `haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩`. Set `L : LabelDatum (D.host.g k)` to `⟨D.ntypes.teichC k, D.ntypes.teichC_inj k, T.ζ k, fun d hd => (T.ζ_gen k d hd).1, fun d e hd he => (T.ζ_gen k d hd).2 _ (dvd_mul_right d e) (Nat.mul_pos hd he)⟩`. Take `⟨σ, π, hσ, h1⟩` from `exists_perm hG L (T.O k)`. Establish `h5` using `five_le_typePrime D k`.

Establish `hr` using `rank_eq_k_add_two_mul D.R`. Establish `hk : 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Establish `hw : ∀ a f, IsLabel D k f → wtOf D k a f = wtC L a (ext σ f)`. Introduce `a f hf`. Unfold `wtOf wtC`.

Rewrite using `[T.eSer_def, eSer_eq L (T.O k) hσ h1 h5 hG _ hf.1 hf.2.2]`. Establish `hz : ∀ a f, ¬ IsLabel D k f → wtOf D k a f = 0`. Introduce `a f hf`. Unfold `wtOf`. Rewrite using `[Formalism.L2.eSer_zero_of_tie T k f hf]`.

Simplify using the standard rewrite rules. Take `⟨hU, hU1, hJ, -⟩` from `GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ`. Take `⟨hJ, hJ1⟩` from `hJ hr`. Use `⟨fun f => ?_, fun f hf hs => ?_, fun f hf => ?_, fun f hf hs => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hf : IsLabel D k f`.

Rewrite using `[hw _ _ hf, hw _ _ hf]`. Use `⟨GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime _ L _ _ hU ?_ _, GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime _ L _ _ hJ ?_ _⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `0 ≤ ((eU (D.host.g k) D.R.r ψ).coeff 1).re`. Rewrite using `[hU1, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]`. Check the signs of the components of the expression.

Express the relevant statement in the definitionally equal form `0 ≤ ((eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ).coeff 1).re`. Rewrite using `[hJ1, ← Nat.cast_pow, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]`. Check the signs of the components of the expression. Rewrite using `[hz _ _ hf, hz _ _ hf]`. Conclude with `⟨le_rfl, le_rfl⟩`.

Take `⟨a, b, c, e⟩` from `ext_lab hσ hf.1 hf.2.2`. Rewrite using `[hw _ _ hf]`. Use `(GlobalTheory.T.harishChandraSeriesWeight_squarefree_label_gelfandGraev _ L h5 hG ψ hψ _ _ a (b.trans hf.2.1) c (e hs)).trans ?_` and prove the remaining obligations. Rewrite using `[nf_ext hσ hf.1 hf.2.2, Multiset.map_map]`. Use `congr 2`.

Conclude with `Multiset.map_congr rfl fun P h => by`. Simplify using `only [Function.comp, (hσ _ _ ((nf_lab hf.1 hf.2.2).1 P h)).1.2.2.2]`. Rewrite using `[hw _ _ hf, hw _ _ hf]`. Conclude with `GlobalTheory.T.harishChandraSeriesWeight_lower_comparison _ L ψ hψ _ _ _ hr hk _`. Take `⟨a, b, c, e⟩` from `ext_lab hσ hf.1 hf.2.2`.

Rewrite using `[hw _ _ hf, hw _ _ hf]`. Conclude with `GlobalTheory.T.harishChandraSeriesWeight_le_squarefree _ L h5 hG ψ hψ _ _ _ hr hk _ a (b.trans hf.2.1) c (e hs)`.
-/
theorem admissibleLabelWeights_of_greenCuspidalParametrisation : Green → ∀ (D : D7) (jE : D.host.E →+* Formalism.L2.Host.Qb) (T : Formalism.L2.NormalizedTypesCompatibility D jE), admLq D := by
  intro hG D jE T k ψ hψ
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  let L : LabelDatum (D.host.g k) :=
    ⟨D.ntypes.teichC k, D.ntypes.teichC_inj k, T.ζ k, fun d hd => (T.ζ_gen k d hd).1, fun d e hd he => (T.ζ_gen k d hd).2 _ (dvd_mul_right d e) (Nat.mul_pos hd he)⟩
  obtain ⟨σ, π, hσ, h1⟩ := exists_perm hG L (T.O k)
  have h5 := five_le_typePrime D k
  have hr := rank_eq_k_add_two_mul D.R
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hw : ∀ a f, IsLabel D k f → wtOf D k a f = wtC L a (ext σ f) := by
    intro a f hf
    unfold wtOf wtC
    rw [T.eSer_def, eSer_eq L (T.O k) hσ h1 h5 hG _ hf.1 hf.2.2]
  have hz : ∀ a f, ¬ IsLabel D k f → wtOf D k a f = 0 := by
    intro a f hf
    unfold wtOf
    rw [Formalism.L2.eSer_zero_of_tie T k f hf]
    simp
  obtain ⟨hU, hU1, hJ, -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ
  obtain ⟨hJ, hJ1⟩ := hJ hr
  refine ⟨fun f => ?_, fun f hf hs => ?_, fun f hf => ?_, fun f hf hs => ?_⟩
  · by_cases hf : IsLabel D k f
    · rw [hw _ _ hf, hw _ _ hf]
      refine ⟨GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime _ L _ _ hU ?_ _, GlobalTheory.T.harishChandraSeriesWeight_nonneg_of_idempotent_glnPrime _ L _ _ hJ ?_ _⟩
      · change 0 ≤ ((eU (D.host.g k) D.R.r ψ).coeff 1).re
        rw [hU1, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.ofReal_re]
        positivity
      · change 0 ≤ ((eJ (D.host.g k) D.R.r D.R.k (D.R.m / 2 - 1) ψ).coeff 1).re
        rw [hJ1, ← Nat.cast_pow, ← Nat.cast_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
          ← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
        positivity
    · rw [hz _ _ hf, hz _ _ hf]
      exact ⟨le_rfl, le_rfl⟩
  · obtain ⟨a, b, c, e⟩ := ext_lab hσ hf.1 hf.2.2
    rw [hw _ _ hf]
    refine (GlobalTheory.T.harishChandraSeriesWeight_squarefree_label_gelfandGraev _ L h5 hG ψ hψ _ _ a (b.trans hf.2.1) c (e hs)).trans ?_
    rw [nf_ext hσ hf.1 hf.2.2, Multiset.map_map]
    congr 2
    exact Multiset.map_congr rfl fun P h => by
      simp only [Function.comp, (hσ _ _ ((nf_lab hf.1 hf.2.2).1 P h)).1.2.2.2]
  · rw [hw _ _ hf, hw _ _ hf]
    exact GlobalTheory.T.harishChandraSeriesWeight_lower_comparison _ L ψ hψ _ _ _ hr hk _
  · obtain ⟨a, b, c, e⟩ := ext_lab hσ hf.1 hf.2.2
    rw [hw _ _ hf, hw _ _ hf]
    exact GlobalTheory.T.harishChandraSeriesWeight_le_squarefree _ L h5 hG ψ hψ _ _ _ hr hk _ a (b.trans hf.2.1) c (e hs)

end GlobalTheory.Top.Lq
