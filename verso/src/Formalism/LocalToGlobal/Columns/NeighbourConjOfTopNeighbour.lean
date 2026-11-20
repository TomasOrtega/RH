import Formalism.LocalToGlobal.Columns.CardFilterNeighboursEqPaths

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section ConjLat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

/- English proof (translation)
Take `⟨_, h2, ⟨e⟩⟩` from `h`. Rewrite `h2`, `e` using `[conjIdeal_asIdeal]`. Take `⟨ρ, hρs, hρk⟩` from `exists_redLat hN (conjPrime₂ Q)`. Establish `hle : (conjPrime₂ Q).asIdeal • N ≤ Z ⊓ N` using `le_inf h2 Submodule.smul_le_right`. Use `haveI : Finite (N ⧸ ((conjPrime₂ Q).asIdeal • N).comap N.subtype) := finite_quot_smul N hN.fg _ (conjPrime₂ Q).ne_bot`.

Establish `hpos : 0 < Nat.card (N ⧸ ((conjPrime₂ Q).asIdeal • N).comap N.subtype)` using `Nat.card_pos`. Establish `c1 : Nat.card (N ⧸ ((conjPrime₂ Q).asIdeal • N).comap N.subtype) = Nat.card (Fin n → 𝓞 E ⧸ (conjPrime₂ Q).asIdeal)`. Rewrite using `[← hρk]`. Conclude with `Nat.card_congr (ρ.quotKerEquivOfSurjective hρs).toEquiv`. Establish `c2 : Nat.card (N ⧸ (Z ⊓ N).comap N.subtype) = Nat.card (Fin n → 𝓞 E ⧸ (conjPrime₂ Q).asIdeal)` using `Nat.card_congr e.toEquiv`.

Rewrite `c1` using `[← c2]`. Rewrite `c1` using `[wmp_card_quot, wmp_card_quot]`. Rewrite `hpos` using `[wmp_card_quot]`. Establish `hm` using `AddSubgroup.relIndex_mul_relIndex ((conjPrime₂ Q).asIdeal • N).toAddSubgroup (Z ⊓ N).toAddSubgroup N.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).mpr hle) ((Submodule.toAddSubgroup_le _ _).mpr inf_le_right)`. Rewrite `hm`, `hpos` using `[c1]`.

Establish `h1 : ((conjPrime₂ Q).asIdeal • N).toAddSubgroup.relIndex (Z ⊓ N).toAddSubgroup = 1` using `Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hm)`. Conclude with `le_antisymm ((Submodule.toAddSubgroup_le _ _).mp (AddSubgroup.relIndex_eq_one.mp h1)) hle`.
-/
theorem topNeighbour_inf_eq (Q : HeightOneSpectrum (𝓞 E)) {N Z : Submodule (𝓞 E) (Sp E n)} (hN : Submodule.IsLattice E N)
    (h : IsHeckeNbr Q.asIdeal n N Z) : Z ⊓ N = (conjPrime₂ Q).asIdeal • N := by
  obtain ⟨_, h2, ⟨e⟩⟩ := h
  rw [conjIdeal_asIdeal] at h2 e
  obtain ⟨ρ, hρs, hρk⟩ := exists_redLat hN (conjPrime₂ Q)
  have hle : (conjPrime₂ Q).asIdeal • N ≤ Z ⊓ N := le_inf h2 Submodule.smul_le_right
  haveI : Finite (N ⧸ ((conjPrime₂ Q).asIdeal • N).comap N.subtype) :=
    finite_quot_smul N hN.fg _ (conjPrime₂ Q).ne_bot
  have hpos : 0 < Nat.card (N ⧸ ((conjPrime₂ Q).asIdeal • N).comap N.subtype) := Nat.card_pos
  have c1 : Nat.card (N ⧸ ((conjPrime₂ Q).asIdeal • N).comap N.subtype) =
      Nat.card (Fin n → 𝓞 E ⧸ (conjPrime₂ Q).asIdeal) := by
    rw [← hρk]
    exact Nat.card_congr (ρ.quotKerEquivOfSurjective hρs).toEquiv
  have c2 : Nat.card (N ⧸ (Z ⊓ N).comap N.subtype) = Nat.card (Fin n → 𝓞 E ⧸ (conjPrime₂ Q).asIdeal) :=
    Nat.card_congr e.toEquiv
  rw [← c2] at c1
  rw [wmp_card_quot, wmp_card_quot] at c1
  rw [wmp_card_quot] at hpos
  have hm := AddSubgroup.relIndex_mul_relIndex ((conjPrime₂ Q).asIdeal • N).toAddSubgroup
    (Z ⊓ N).toAddSubgroup N.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).mpr hle)
    ((Submodule.toAddSubgroup_le _ _).mpr inf_le_right)
  rw [c1] at hm hpos
  have h1 : ((conjPrime₂ Q).asIdeal • N).toAddSubgroup.relIndex (Z ⊓ N).toAddSubgroup = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [one_mul]; exact hm)
  exact le_antisymm ((Submodule.toAddSubgroup_le _ _).mp (AddSubgroup.relIndex_eq_one.mp h1)) hle

/- English proof (translation)
Rewrite using `[← topNeighbour_inf_eq Q hN h]`. Conclude with `IsHeckeNbr.eq_glue hN huN huZ Q hne h`.
-/
theorem topNeighbour_eq_glue (Q : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ Q ≠ Q) {N Z : Submodule (𝓞 E) (Sp E n)}
    (hN : Submodule.IsLattice E N) (huN : IsUnimodular (hStd E n) N) (huZ : IsUnimodular (hStd E n) Z)
    (h : IsHeckeNbr Q.asIdeal n N Z) :
    Z = (conjPrime₂ Q).asIdeal • N ⊔ (conjPrime₂ Q).asIdeal • dual (hStd E n) ((conjPrime₂ Q).asIdeal • N) := by
  rw [← topNeighbour_inf_eq Q hN h]
  exact IsHeckeNbr.eq_glue hN huN huZ Q hne h

/- English proof (translation)
Establish `h2` using `hH.2.1`. Rewrite `h2` using `[conjIdeal_asIdeal]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ideal_smul_topNeighbour_le (Q : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ Q ≠ Q) {N Z H : Submodule (𝓞 E) (Sp E n)} {j : ℕ}
    (hN : Submodule.IsLattice E N) (huN : IsUnimodular (hStd E n) N) (huZ : IsUnimodular (hStd E n) Z)
    (huH : IsUnimodular (hStd E n) H) (hZ : IsHeckeNbr Q.asIdeal n N Z) (hH : IsHeckeNbr Q.asIdeal j N H) :
    Q.asIdeal • Z ≤ H := by
  have h2 := hH.2.1
  rw [conjIdeal_asIdeal] at h2
  calc Q.asIdeal • Z ≤ Z ⊓ N := le_inf Submodule.smul_le_right hZ.1
    _ = (conjPrime₂ Q).asIdeal • N := topNeighbour_inf_eq Q hN hZ
    _ ≤ H := h2

/- English proof (translation)
Establish `hd` using `dual_anti h`. Rewrite `hd` using `[show dual (hStd E n) H = H from huH]`. Use `Submodule.smul_le.mpr fun r hr x hx => ?_` and prove the remaining obligations. Establish `hr' : cO E r ∈ Q.asIdeal` using `Ideal.mem_comap.mp hr`. Establish `hx'` using `(mem_dual_smul Q.asIdeal Z x).mp (hd hx) (cO E r) hr'`.

Rewrite `hx'` using `[cO_cO, show dual (hStd E n) Z = Z from huZ]`. Conclude with `hx'`.
-/
theorem dual_ideal_smul_le (Q : HeightOneSpectrum (𝓞 E)) {Z H : Submodule (𝓞 E) (Sp E n)}
    (huZ : IsUnimodular (hStd E n) Z) (huH : IsUnimodular (hStd E n) H) (h : Q.asIdeal • Z ≤ H) :
    (conjPrime₂ Q).asIdeal • H ≤ Z := by
  have hd := dual_anti h
  rw [show dual (hStd E n) H = H from huH] at hd
  refine Submodule.smul_le.mpr fun r hr x hx => ?_
  have hr' : cO E r ∈ Q.asIdeal := Ideal.mem_comap.mp hr
  have hx' := (mem_dual_smul Q.asIdeal Z x).mp (hd hx) (cO E r) hr'
  rw [cO_cO, show dual (hStd E n) Z = Z from huZ] at hx'
  exact hx'

/- English proof (translation)
Establish `hQZ` using `ideal_smul_topNeighbour_le Q hne hN huN huZ huH hZ hH`. Establish `hQbH` using `dual_ideal_smul_le Q huZ huH hQZ`. Unfold `IsHeckeNbr`. Use `⟨hQbH, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[conjIdeal_asIdeal, conjugatePrime_conjugatePrime]`.

Conclude with `hQZ`. Rewrite using `[conjIdeal_asIdeal, conjugatePrime_conjugatePrime]`. Establish `hinf` using `topNeighbour_inf_eq Q hN hZ`. Use `haveI : Finite (𝓞 E ⧸ Q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot Q.asIdeal Q.ne_bot`. Establish `hq : 0 < Nat.card (𝓞 E ⧸ Q.asIdeal)` using `Nat.card_pos`.

Establish `hZs` using `wmp_isHeckeNbr_symm hN hZl huN huZ hZ`. Establish `hHs` using `wmp_isHeckeNbr_symm hN hHl huN huH hH`. Unfold `IsHeckeNbr at hZs hHs`. Rewrite `hZs`, `hHs` using `[conjIdeal_asIdeal, conjugatePrime_conjugatePrime]`. Take `⟨eZ⟩` from `hZs.2.2`.

Take `⟨eH⟩` from `hHs.2.2`. Establish `cZ : (N ⊓ Z).toAddSubgroup.relIndex Z.toAddSubgroup = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ n`. Rewrite using `[← wmp_card_quot, Nat.card_congr eZ.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]`. Establish `cH : (N ⊓ H).toAddSubgroup.relIndex H.toAddSubgroup = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ j`. Rewrite using `[← wmp_card_quot, Nat.card_congr eH.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin j), Fintype.card_fin]`.

Establish `hQbN_H : (conjPrime₂ Q).asIdeal • N ≤ H`. Use `hH.2.1` as an intermediate fact. Rewrite `this` using `[conjIdeal_asIdeal]`. Then use the resulting hypothesis. Establish `hQbN_Z : (conjPrime₂ Q).asIdeal • N ≤ Z`. Use `hZ.2.1` as an intermediate fact.

Rewrite `this` using `[conjIdeal_asIdeal]`. Then use the resulting hypothesis. Establish `hQbN_N : (conjPrime₂ Q).asIdeal • N ≤ N` using `Submodule.smul_le_right`. Establish `hint : (Z ⊓ H) ⊓ (N ⊓ H) = (conjPrime₂ Q).asIdeal • N`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hinf]`.

Conclude with `le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)`. Conclude with `le_inf (le_inf hQbN_Z hQbN_H) (le_inf hQbN_N hQbN_H)`. Establish `hcop : Q.asIdeal ⊔ (conjPrime₂ Q).asIdeal = ⊤`. Use `Ideal.IsMaximal.coprime_of_ne Q.isMaximal (conjPrime₂ Q).isMaximal ?_` and prove the remaining obligations. Introduce `h`.

Conclude with `hne (IsDedekindDomain.HeightOneSpectrum.ext h.symm)`. Establish `hsup : (Z ⊓ H) ⊔ (N ⊓ H) = H`. Use `le_antisymm (sup_le inf_le_right inf_le_right) ?_` and prove the remaining obligations. Introduce `x hx`. Establish `h1 : (1 : 𝓞 E) ∈ Q.asIdeal ⊔ (conjPrime₂ Q).asIdeal`.

Rewrite using `[hcop]`. Conclude with `Submodule.mem_top`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.mp h1`. Establish `hx' : x = b • x + a • x`. Rewrite using `[← add_smul, add_comm b a, hab, one_smul]`.

Rewrite using `[hx']`. Use `Submodule.add_mem_sup ⟨hQbH (Submodule.smul_mem_smul hb hx), H.smul_mem b hx⟩ ⟨hH.1 (Submodule.smul_mem_smul ha hx), H.smul_mem a hx⟩` and prove the remaining obligations. Establish `c2` using `Nat.card_congr (LinearMap.quotientInfEquivSupQuotient (Z ⊓ H) (N ⊓ H)).toEquiv`. Rewrite `c2` using `[← Submodule.comap_inf, wmp_card_quot, wmp_card_quot, hint, hsup]`. Establish `hm` using `AddSubgroup.relIndex_mul_relIndex ((conjPrime₂ Q).asIdeal • N).toAddSubgroup (Z ⊓ H).toAddSubgroup Z.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).mpr (le_inf hQbN_Z hQbN_H)) ((Submodule.toAddSubgroup_le _ _).mpr inf_le_left)`.

Rewrite `hm` using `[c2, cH, ← hinf, inf_comm Z N, cZ]`. Establish `hx : (H ⊓ Z).toAddSubgroup.relIndex Z.toAddSubgroup = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (n - j)`. Rewrite using `[inf_comm H Z]`. Establish `hpow : Nat.card (𝓞 E ⧸ Q.asIdeal) ^ n = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ j * Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (n - j)`. Rewrite using `[← pow_add, Nat.add_sub_cancel' hj]`.

Rewrite `hm` using `[hpow]`. Conclude with `Nat.eq_of_mul_eq_mul_left (pow_pos hq j) hm`. Use `wmp_quot_equiv_of_card Q _ ?_ ?_` and prove the remaining obligations. Introduce `p hp x`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨hQZ (Submodule.smul_mem_smul hp z.2), (p • z).2⟩`. Rewrite using `[wmp_card_quot, hx]`.
-/
theorem neighbour_conj_of_topNeighbour (Q : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ Q ≠ Q) {N Z H : Submodule (𝓞 E) (Sp E n)} {j : ℕ} (hj : j ≤ n)
    (hN : Submodule.IsLattice E N) (hZl : Submodule.IsLattice E Z) (hHl : Submodule.IsLattice E H)
    (huN : IsUnimodular (hStd E n) N) (huZ : IsUnimodular (hStd E n) Z)
    (huH : IsUnimodular (hStd E n) H) (hZ : IsHeckeNbr Q.asIdeal n N Z) (hH : IsHeckeNbr Q.asIdeal j N H) :
    IsHeckeNbr (conjPrime₂ Q).asIdeal (n - j) Z H := by
  have hQZ := ideal_smul_topNeighbour_le Q hne hN huN huZ huH hZ hH
  have hQbH := dual_ideal_smul_le Q huZ huH hQZ
  unfold IsHeckeNbr
  refine ⟨hQbH, ?_, ?_⟩
  · rw [conjIdeal_asIdeal, conjugatePrime_conjugatePrime]
    exact hQZ
  · rw [conjIdeal_asIdeal, conjugatePrime_conjugatePrime]
    have hinf := topNeighbour_inf_eq Q hN hZ
    haveI : Finite (𝓞 E ⧸ Q.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot Q.asIdeal Q.ne_bot
    have hq : 0 < Nat.card (𝓞 E ⧸ Q.asIdeal) := Nat.card_pos
    have hZs := wmp_isHeckeNbr_symm hN hZl huN huZ hZ
    have hHs := wmp_isHeckeNbr_symm hN hHl huN huH hH
    unfold IsHeckeNbr at hZs hHs
    rw [conjIdeal_asIdeal, conjugatePrime_conjugatePrime] at hZs hHs
    obtain ⟨eZ⟩ := hZs.2.2
    obtain ⟨eH⟩ := hHs.2.2
    have cZ : (N ⊓ Z).toAddSubgroup.relIndex Z.toAddSubgroup = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ n := by
      rw [← wmp_card_quot, Nat.card_congr eZ.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n),
        Fintype.card_fin]
    have cH : (N ⊓ H).toAddSubgroup.relIndex H.toAddSubgroup = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ j := by
      rw [← wmp_card_quot, Nat.card_congr eH.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin j),
        Fintype.card_fin]
    have hQbN_H : (conjPrime₂ Q).asIdeal • N ≤ H := by
      have := hH.2.1
      rwa [conjIdeal_asIdeal] at this
    have hQbN_Z : (conjPrime₂ Q).asIdeal • N ≤ Z := by
      have := hZ.2.1
      rwa [conjIdeal_asIdeal] at this
    have hQbN_N : (conjPrime₂ Q).asIdeal • N ≤ N := Submodule.smul_le_right
    have hint : (Z ⊓ H) ⊓ (N ⊓ H) = (conjPrime₂ Q).asIdeal • N := by
      apply le_antisymm
      · rw [← hinf]
        exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
      · exact le_inf (le_inf hQbN_Z hQbN_H) (le_inf hQbN_N hQbN_H)
    have hcop : Q.asIdeal ⊔ (conjPrime₂ Q).asIdeal = ⊤ := by
      refine Ideal.IsMaximal.coprime_of_ne Q.isMaximal (conjPrime₂ Q).isMaximal ?_
      intro h
      exact hne (IsDedekindDomain.HeightOneSpectrum.ext h.symm)
    have hsup : (Z ⊓ H) ⊔ (N ⊓ H) = H := by
      refine le_antisymm (sup_le inf_le_right inf_le_right) ?_
      intro x hx
      have h1 : (1 : 𝓞 E) ∈ Q.asIdeal ⊔ (conjPrime₂ Q).asIdeal := by
        rw [hcop]
        exact Submodule.mem_top
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp h1
      have hx' : x = b • x + a • x := by
        rw [← add_smul, add_comm b a, hab, one_smul]
      rw [hx']
      refine Submodule.add_mem_sup ⟨hQbH (Submodule.smul_mem_smul hb hx), H.smul_mem b hx⟩
        ⟨hH.1 (Submodule.smul_mem_smul ha hx), H.smul_mem a hx⟩
    have c2 := Nat.card_congr (LinearMap.quotientInfEquivSupQuotient (Z ⊓ H) (N ⊓ H)).toEquiv
    rw [← Submodule.comap_inf, wmp_card_quot, wmp_card_quot, hint, hsup] at c2
    have hm := AddSubgroup.relIndex_mul_relIndex ((conjPrime₂ Q).asIdeal • N).toAddSubgroup
      (Z ⊓ H).toAddSubgroup Z.toAddSubgroup ((Submodule.toAddSubgroup_le _ _).mpr (le_inf hQbN_Z hQbN_H))
      ((Submodule.toAddSubgroup_le _ _).mpr inf_le_left)
    rw [c2, cH, ← hinf, inf_comm Z N, cZ] at hm
    have hx : (H ⊓ Z).toAddSubgroup.relIndex Z.toAddSubgroup = Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (n - j) := by
      rw [inf_comm H Z]
      have hpow : Nat.card (𝓞 E ⧸ Q.asIdeal) ^ n =
          Nat.card (𝓞 E ⧸ Q.asIdeal) ^ j * Nat.card (𝓞 E ⧸ Q.asIdeal) ^ (n - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hj]
      rw [hpow] at hm
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hq j) hm
    refine wmp_quot_equiv_of_card Q _ ?_ ?_
    · intro p hp x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨hQZ (Submodule.smul_mem_smul hp z.2), (p • z).2⟩
    · rw [wmp_card_quot, hx]

end ConjLat

section ConjDeco

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp [gaussBin]`. Consider the case `succ k ih => simp only [gaussBin, ih, gaussBin_eq_zero q (Nat.lt_succ_self k), mul_zero, add_zero]`.
-/
theorem gaussBinomial_self (q n : ℕ) : gaussBin q n n = 1 := by
  induction n with
  | zero => simp [gaussBin]
  | succ k ih => simp only [gaussBin, ih, gaussBin_eq_zero q (Nat.lt_succ_self k), mul_zero, add_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hf, hb⟩`. Conclude with `⟨wmp_isHeckeNbr_symm d.2.lat e.2.lat d.2.uni e.2.uni h, hf.symm, hb.symm⟩`. Introduce and unpack `⟨h, hf, hb⟩`. Establish `h'` using `wmp_isHeckeNbr_symm e.2.lat d.2.lat e.2.uni d.2.uni h`.

Rewrite `h'` using `[conjugatePrime_conjugatePrime]`. Conclude with `⟨h', hf.symm, hb.symm⟩`.
-/
theorem mem_heckeSet_iff_symm (Q : HeightOneSpectrum (𝓞 E)) {i : ℕ} (d e : DecoSet E n ST SG) :
    e ∈ d.heckeSet Q.asIdeal i ↔ d ∈ e.heckeSet (conjPrime₂ Q).asIdeal i := by
  constructor
  · rintro ⟨h, hf, hb⟩
    exact ⟨wmp_isHeckeNbr_symm d.2.lat e.2.lat d.2.uni e.2.uni h, hf.symm, hb.symm⟩
  · rintro ⟨h, hf, hb⟩
    have h' := wmp_isHeckeNbr_symm e.2.lat d.2.lat e.2.uni d.2.uni h
    rw [conjugatePrime_conjugatePrime] at h'
    exact ⟨h', hf.symm, hb.symm⟩

open Classical in

def decoratedNeighbourAtPrime (Q : HeightOneSpectrum (𝓞 E)) (g : DecoSet E n ST SG) : DecoSet E n ST SG :=
  if h : (g.heckeSet Q.asIdeal n).Nonempty then h.some else g

/- English proof (translation)
Rewrite using `[DecoSet.card_heckeSet g Q hne hST hSG n, gaussBinomial_self]`.
-/
theorem card_topNeighbours_eq_one (Q : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ Q ≠ Q) (hST : ∀ R : ST, R.1 ≠ Q ∧ R.1 ≠ conjPrime₂ Q)
    (hSG : ∀ w : SG, w.1 ≠ Q ∧ w.1 ≠ conjPrime₂ Q) (g : DecoSet E n ST SG) : Nat.card (g.heckeSet Q.asIdeal n) = 1 := by
  rw [DecoSet.card_heckeSet g Q hne hST hSG n, gaussBinomial_self]

/- English proof (translation)
Establish `hc` using `card_topNeighbours_eq_one Q hne hST hSG g`. Establish `hn : (g.heckeSet Q.asIdeal n).Nonempty` using `Set.nonempty_coe_sort.mp (Nat.card_eq_one_iff_unique.mp hc).2`. Unfold `decoratedNeighbourAtPrime`. Rewrite using `[dif_pos hn]`. Conclude with `hn.some_mem`.
-/
theorem topNeighbour_mem (Q : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ Q ≠ Q) (hST : ∀ R : ST, R.1 ≠ Q ∧ R.1 ≠ conjPrime₂ Q)
    (hSG : ∀ w : SG, w.1 ≠ Q ∧ w.1 ≠ conjPrime₂ Q) (g : DecoSet E n ST SG) : decoratedNeighbourAtPrime Q g ∈ g.heckeSet Q.asIdeal n := by
  have hc := card_topNeighbours_eq_one Q hne hST hSG g
  have hn : (g.heckeSet Q.asIdeal n).Nonempty :=
    Set.nonempty_coe_sort.mp (Nat.card_eq_one_iff_unique.mp hc).2
  unfold decoratedNeighbourAtPrime
  rw [dif_pos hn]
  exact hn.some_mem

/- English proof (translation)
Establish `hc` using `card_topNeighbours_eq_one Q hne hST hSG g`. Establish `hs` using `(Nat.card_eq_one_iff_unique.mp hc).1`. Establish `hm` using `topNeighbour_mem Q hne hST hSG g`. Conclude with `congrArg Subtype.val (@Subsingleton.elim _ hs ⟨z, hz⟩ ⟨_, hm⟩)`.
-/
theorem topNeighbour_unique (Q : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ Q ≠ Q) (hST : ∀ R : ST, R.1 ≠ Q ∧ R.1 ≠ conjPrime₂ Q)
    (hSG : ∀ w : SG, w.1 ≠ Q ∧ w.1 ≠ conjPrime₂ Q) {g z : DecoSet E n ST SG} (hz : z ∈ g.heckeSet Q.asIdeal n) :
    z = decoratedNeighbourAtPrime Q g := by
  have hc := card_topNeighbours_eq_one Q hne hST hSG g
  have hs := (Nat.card_eq_one_iff_unique.mp hc).1
  have hm := topNeighbour_mem Q hne hST hSG g
  exact congrArg Subtype.val (@Subsingleton.elim _ hs ⟨z, hz⟩ ⟨_, hm⟩)

/- English proof (translation)
Take `⟨hz1, hz2, hz3⟩` from `hz`. Take `⟨hh1, hh2, hh3⟩` from `hh`. Conclude with `⟨neighbour_conj_of_topNeighbour Q hne hj g.2.lat z.2.lat h.2.lat g.2.uni z.2.uni h.2.uni hz1 hh1, hh2.trans hz2.symm, hh3.trans hz3.symm⟩`.
-/
theorem neighbour_of_topNeighbour_sub (Q : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ Q ≠ Q) {g z h : DecoSet E n ST SG} {j : ℕ} (hj : j ≤ n)
    (hz : z ∈ g.heckeSet Q.asIdeal n) (hh : h ∈ g.heckeSet Q.asIdeal j) : h ∈ z.heckeSet (conjPrime₂ Q).asIdeal (n - j) := by
  obtain ⟨hz1, hz2, hz3⟩ := hz
  obtain ⟨hh1, hh2, hh3⟩ := hh
  exact ⟨neighbour_conj_of_topNeighbour Q hne hj g.2.lat z.2.lat h.2.lat g.2.uni z.2.uni h.2.uni hz1 hh1, hh2.trans hz2.symm,
    hh3.trans hz3.symm⟩

variable (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P) (hST : ∀ R : ST, R.1 ≠ P ∧ R.1 ≠ conjPrime₂ P)
  (hSG : ∀ w : SG, w.1 ≠ P ∧ w.1 ≠ conjPrime₂ P)
include hne hST hSG

/- English proof (translation)
Apply the tactic sequence `refine ⟨?_, fun R => ?_, fun w => ?_⟩ <;> rw [conjugatePrime_conjugatePrime]`. Conclude with `Ne.symm hne`. Conclude with `⟨(hST R).2, (hST R).1⟩`. Conclude with `⟨(hSG w).2, (hSG w).1⟩`.
-/
theorem conj_split_hypotheses : conjPrime₂ (conjPrime₂ P) ≠ conjPrime₂ P ∧ (∀ R : ST, R.1 ≠ conjPrime₂ P ∧ R.1 ≠ conjPrime₂ (conjPrime₂ P)) ∧
    (∀ w : SG, w.1 ≠ conjPrime₂ P ∧ w.1 ≠ conjPrime₂ (conjPrime₂ P)) := by
  refine ⟨?_, fun R => ?_, fun w => ?_⟩ <;> rw [conjugatePrime_conjugatePrime]
  · exact Ne.symm hne
  · exact ⟨(hST R).2, (hST R).1⟩
  · exact ⟨(hSG w).2, (hSG w).1⟩

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `conj_split_hypotheses P hne hST hSG`. Establish `hz` using `topNeighbour_mem (conjPrime₂ P) h1 h2 h3 g`. Use extensionality with `h`. Prove the components needed by the constructor for the conclusion. Introduce `hh`.

Use `neighbour_of_topNeighbour_sub (conjPrime₂ P) h1 hj hz hh` as an intermediate fact. Rewrite `this` using `[conjugatePrime_conjugatePrime]`. Then use the resulting hypothesis. Introduce `hh`. Establish `hg : g ∈ (decoratedNeighbourAtPrime (conjPrime₂ P) g).heckeSet P.asIdeal n`. Use `(mem_heckeSet_iff_symm (conjPrime₂ P) g (decoratedNeighbourAtPrime (conjPrime₂ P) g)).mp hz` as an intermediate fact.

Rewrite `this` using `[conjugatePrime_conjugatePrime]`. Then use the resulting hypothesis. Use `neighbour_of_topNeighbour_sub P hne (Nat.sub_le n j) hg hh` as an intermediate fact. Rewrite `this` using `[Nat.sub_sub_self hj]`. Then use the resulting hypothesis.
-/
theorem heckeSet_conj_eq_topNeighbour {j : ℕ} (hj : j ≤ n) (g : DecoSet E n ST SG) :
    g.heckeSet (conjPrime₂ P).asIdeal j = (decoratedNeighbourAtPrime (conjPrime₂ P) g).heckeSet P.asIdeal (n - j) := by
  obtain ⟨h1, h2, h3⟩ := conj_split_hypotheses P hne hST hSG
  have hz := topNeighbour_mem (conjPrime₂ P) h1 h2 h3 g
  ext h
  constructor
  · intro hh
    have := neighbour_of_topNeighbour_sub (conjPrime₂ P) h1 hj hz hh
    rwa [conjugatePrime_conjugatePrime] at this
  · intro hh
    have hg : g ∈ (decoratedNeighbourAtPrime (conjPrime₂ P) g).heckeSet P.asIdeal n := by
      have := (mem_heckeSet_iff_symm (conjPrime₂ P) g (decoratedNeighbourAtPrime (conjPrime₂ P) g)).mp hz
      rwa [conjugatePrime_conjugatePrime] at this
    have := neighbour_of_topNeighbour_sub P hne (Nat.sub_le n j) hg hh
    rwa [Nat.sub_sub_self hj] at this

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `conj_split_hypotheses P hne hST hSG`. Establish `hZZ : ∀ g : DecoSet E n ST SG, decoratedNeighbourAtPrime P (decoratedNeighbourAtPrime (conjPrime₂ P) g) = g`. Introduce `g`. Establish `hz` using `topNeighbour_mem (conjPrime₂ P) h1 h2 h3 g`. Establish `hg` using `(mem_heckeSet_iff_symm (conjPrime₂ P) g (decoratedNeighbourAtPrime (conjPrime₂ P) g)).mp hz`.

Rewrite `hg` using `[conjugatePrime_conjugatePrime]`. Conclude with `(topNeighbour_unique P hne hST hSG hg).symm`. Establish `hB` using `heckeSet_conj_eq_topNeighbour P hne hST hSG (Nat.sub_le n i) d`. Rewrite `hB` using `[Nat.sub_sub_self hi]`. Establish `hB'` using `heckeSet_conj_eq_topNeighbour (conjPrime₂ P) h1 h2 h3 (Nat.sub_le n i) (decoratedNeighbourAtPrime (conjPrime₂ P) e)`.

Rewrite `hB'` using `[conjugatePrime_conjugatePrime, Nat.sub_sub_self hi, hZZ]`. Rewrite using `[← hB, mem_heckeSet_iff_symm (conjPrime₂ P) d (decoratedNeighbourAtPrime (conjPrime₂ P) e), conjugatePrime_conjugatePrime, hB', ← mem_heckeSet_iff_symm P d e]`.
-/
theorem mem_heckeSet_iff_topNeighbour {i : ℕ} (hi : i ≤ n) (d e : DecoSet E n ST SG) :
    e ∈ d.heckeSet P.asIdeal i ↔ decoratedNeighbourAtPrime (conjPrime₂ P) e ∈ (decoratedNeighbourAtPrime (conjPrime₂ P) d).heckeSet P.asIdeal i := by
  obtain ⟨h1, h2, h3⟩ := conj_split_hypotheses P hne hST hSG
  have hZZ : ∀ g : DecoSet E n ST SG, decoratedNeighbourAtPrime P (decoratedNeighbourAtPrime (conjPrime₂ P) g) = g := by
    intro g
    have hz := topNeighbour_mem (conjPrime₂ P) h1 h2 h3 g
    have hg := (mem_heckeSet_iff_symm (conjPrime₂ P) g (decoratedNeighbourAtPrime (conjPrime₂ P) g)).mp hz
    rw [conjugatePrime_conjugatePrime] at hg
    exact (topNeighbour_unique P hne hST hSG hg).symm
  have hB := heckeSet_conj_eq_topNeighbour P hne hST hSG (Nat.sub_le n i) d
  rw [Nat.sub_sub_self hi] at hB
  have hB' := heckeSet_conj_eq_topNeighbour (conjPrime₂ P) h1 h2 h3 (Nat.sub_le n i) (decoratedNeighbourAtPrime (conjPrime₂ P) e)
  rw [conjugatePrime_conjugatePrime, Nat.sub_sub_self hi, hZZ] at hB'
  rw [← hB, mem_heckeSet_iff_symm (conjPrime₂ P) d (decoratedNeighbourAtPrime (conjPrime₂ P) e), conjugatePrime_conjugatePrime, hB',
    ← mem_heckeSet_iff_symm P d e]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `conj_split_hypotheses P hne hST hSG`. Establish `hz` using `topNeighbour_mem P hne hST hSG g`. Establish `hg` using `(mem_heckeSet_iff_symm P g (decoratedNeighbourAtPrime P g)).mp hz`. Conclude with `(topNeighbour_unique (conjPrime₂ P) h1 h2 h3 hg).symm`.
-/
theorem topNeighbour_conj_involutive (g : DecoSet E n ST SG) : decoratedNeighbourAtPrime (conjPrime₂ P) (decoratedNeighbourAtPrime P g) = g := by
  obtain ⟨h1, h2, h3⟩ := conj_split_hypotheses P hne hST hSG
  have hz := topNeighbour_mem P hne hST hSG g
  have hg := (mem_heckeSet_iff_symm P g (decoratedNeighbourAtPrime P g)).mp hz
  exact (topNeighbour_unique (conjPrime₂ P) h1 h2 h3 hg).symm

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `conj_split_hypotheses P hne hST hSG`. Establish `hz` using `topNeighbour_mem (conjPrime₂ P) h1 h2 h3 g`. Establish `hg` using `(mem_heckeSet_iff_symm (conjPrime₂ P) g (decoratedNeighbourAtPrime (conjPrime₂ P) g)).mp hz`. Rewrite `hg` using `[conjugatePrime_conjugatePrime]`. Conclude with `(topNeighbour_unique P hne hST hSG hg).symm`.
-/
theorem topNeighbour_involutive_conj (g : DecoSet E n ST SG) : decoratedNeighbourAtPrime P (decoratedNeighbourAtPrime (conjPrime₂ P) g) = g := by
  obtain ⟨h1, h2, h3⟩ := conj_split_hypotheses P hne hST hSG
  have hz := topNeighbour_mem (conjPrime₂ P) h1 h2 h3 g
  have hg := (mem_heckeSet_iff_symm (conjPrime₂ P) g (decoratedNeighbourAtPrime (conjPrime₂ P) g)).mp hz
  rw [conjugatePrime_conjugatePrime] at hg
  exact (topNeighbour_unique P hne hST hSG hg).symm

omit hne hST hSG in
/- English proof (translation)
Unfold `DecoSet.heckeNb`. Use `split_ifs with hfin`. Establish `hc` using `DecoSet.card_heckeSet g Q hneQ hSTQ hSGQ i`. Rewrite `hc` using `[gaussBin_eq_zero _ hi]`. Use `haveI := hfin.to_subtype`.

Establish `hemp : g.heckeSet Q.asIdeal i = ∅`. Break down `Nat.card_eq_zero.mp hc with hc | hc` into its components or cases. Conclude with `Set.isEmpty_coe_sort.mp hc`. Conclude with `absurd hfin (Set.infinite_coe_iff.mp hc)`. Conclude with `Set.Finite.toFinset_eq_empty.mpr hemp`.

Both sides reduce to the same expression.
-/
theorem heckeNeighbour_empty_of_gt (Q : HeightOneSpectrum (𝓞 E)) (hneQ : conjPrime₂ Q ≠ Q) (hSTQ : ∀ R : ST, R.1 ≠ Q ∧ R.1 ≠ conjPrime₂ Q)
    (hSGQ : ∀ w : SG, w.1 ≠ Q ∧ w.1 ≠ conjPrime₂ Q) {i : ℕ} (hi : n < i) (g : DecoSet E n ST SG) :
    g.heckeNb Q.asIdeal i = ∅ := by
  unfold DecoSet.heckeNb
  split_ifs with hfin
  · have hc := DecoSet.card_heckeSet g Q hneQ hSTQ hSGQ i
    rw [gaussBin_eq_zero _ hi] at hc
    haveI := hfin.to_subtype
    have hemp : g.heckeSet Q.asIdeal i = ∅ := by
      rcases Nat.card_eq_zero.mp hc with hc | hc
      · exact Set.isEmpty_coe_sort.mp hc
      · exact absurd hfin (Set.infinite_coe_iff.mp hc)
    exact Set.Finite.toFinset_eq_empty.mpr hemp
  · rfl

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `conj_split_hypotheses P hne hST hSG`. Establish `hPb : ∀ (Q : HeightOneSpectrum (𝓞 E)) (k : ℕ) (a b : DecoSet E n ST SG), b ∈ a.heckeNb Q.asIdeal k ↔ b ∈ a.heckeSet Q.asIdeal k` using `fun Q k a b => DecoSet.mem_heckeNb Q.ne_bot (by rw [conjIdeal_asIdeal]; exact (conjPrime₂ Q).ne_bot) k a b`. Distinguish the cases in `hi : i ≤ n`. Use `swap`. Simplify using `[decorationPathCount, heckeNeighbour_empty_of_gt P hne hST hSG (not_le.mp hi)]`.

Distinguish the cases in `hj : j ≤ n`. Use `swap`. Simplify using `[decorationPathCount, heckeNeighbour_empty_of_gt (conjPrime₂ P) h1 h2 h3 (not_le.mp hj)]`. Establish `hL : decorationPathCount P.asIdeal (conjPrime₂ P).asIdeal i j d f = decorationPathCount P.asIdeal P.asIdeal i (n - j) (decoratedNeighbourAtPrime (conjPrime₂ P) d) f`. Unfold `decorationPathCount`.

Apply `Finset.card_nbij' (fun e => decoratedNeighbourAtPrime (conjPrime₂ P) e) (fun e => decoratedNeighbourAtPrime P e)` to reduce the goal to its premises. Introduce `e he`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, hPb] at he ⊢`. Use `⟨(mem_heckeSet_iff_topNeighbour P hne hST hSG hi d e).mp he.1, ?_⟩` and prove the remaining obligations. Rewrite using `[← heckeSet_conj_eq_topNeighbour P hne hST hSG hj e]`.

Conclude with `he.2`. Introduce `e he`. Simplify using `only [Finset.mem_coe, Finset.mem_filter, hPb] at he ⊢`. Use `⟨(mem_heckeSet_iff_topNeighbour P hne hST hSG hi d (decoratedNeighbourAtPrime P e)).mpr ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[topNeighbour_conj_involutive P hne hST hSG]`.

Conclude with `he.1`. Rewrite using `[heckeSet_conj_eq_topNeighbour P hne hST hSG hj (decoratedNeighbourAtPrime P e), topNeighbour_conj_involutive P hne hST hSG]`. Conclude with `he.2`. Introduce `e _`. Conclude with `topNeighbour_involutive_conj P hne hST hSG e`.

Introduce `e _`. Conclude with `topNeighbour_conj_involutive P hne hST hSG e`. Establish `hR : decorationPathCount (conjPrime₂ P).asIdeal P.asIdeal j i d f = decorationPathCount P.asIdeal P.asIdeal (n - j) i (decoratedNeighbourAtPrime (conjPrime₂ P) d) f`. Unfold `decorationPathCount`. Use `congr 1`.

Use extensionality with `e`. Simplify using `only [Finset.mem_filter, hPb]`. Rewrite using `[heckeSet_conj_eq_topNeighbour P hne hST hSG hj d]`. Rewrite using `[hL, hR]`. Conclude with `hsame i (n - j) (decoratedNeighbourAtPrime (conjPrime₂ P) d) f`.
-/
theorem pathCount_conj_symm
    (hsame : ∀ (i j : ℕ) (d f : DecoSet E n ST SG),
      decorationPathCount P.asIdeal P.asIdeal i j d f = decorationPathCount P.asIdeal P.asIdeal j i d f)
    (i j : ℕ) (d f : DecoSet E n ST SG) :
    decorationPathCount P.asIdeal (conjPrime₂ P).asIdeal i j d f = decorationPathCount (conjPrime₂ P).asIdeal P.asIdeal j i d f := by
  obtain ⟨h1, h2, h3⟩ := conj_split_hypotheses P hne hST hSG
  have hPb : ∀ (Q : HeightOneSpectrum (𝓞 E)) (k : ℕ) (a b : DecoSet E n ST SG),
      b ∈ a.heckeNb Q.asIdeal k ↔ b ∈ a.heckeSet Q.asIdeal k := fun Q k a b =>
    DecoSet.mem_heckeNb Q.ne_bot (by rw [conjIdeal_asIdeal]; exact (conjPrime₂ Q).ne_bot) k a b
  by_cases hi : i ≤ n
  swap
  · simp [decorationPathCount, heckeNeighbour_empty_of_gt P hne hST hSG (not_le.mp hi)]
  by_cases hj : j ≤ n
  swap
  · simp [decorationPathCount, heckeNeighbour_empty_of_gt (conjPrime₂ P) h1 h2 h3 (not_le.mp hj)]
  have hL : decorationPathCount P.asIdeal (conjPrime₂ P).asIdeal i j d f =
      decorationPathCount P.asIdeal P.asIdeal i (n - j) (decoratedNeighbourAtPrime (conjPrime₂ P) d) f := by
    unfold decorationPathCount
    apply Finset.card_nbij' (fun e => decoratedNeighbourAtPrime (conjPrime₂ P) e) (fun e => decoratedNeighbourAtPrime P e)
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_filter, hPb] at he ⊢
      refine ⟨(mem_heckeSet_iff_topNeighbour P hne hST hSG hi d e).mp he.1, ?_⟩
      rw [← heckeSet_conj_eq_topNeighbour P hne hST hSG hj e]
      exact he.2
    · intro e he
      simp only [Finset.mem_coe, Finset.mem_filter, hPb] at he ⊢
      refine ⟨(mem_heckeSet_iff_topNeighbour P hne hST hSG hi d (decoratedNeighbourAtPrime P e)).mpr ?_, ?_⟩
      · rw [topNeighbour_conj_involutive P hne hST hSG]
        exact he.1
      · rw [heckeSet_conj_eq_topNeighbour P hne hST hSG hj (decoratedNeighbourAtPrime P e), topNeighbour_conj_involutive P hne hST hSG]
        exact he.2
    · intro e _
      exact topNeighbour_involutive_conj P hne hST hSG e
    · intro e _
      exact topNeighbour_conj_involutive P hne hST hSG e
  have hR : decorationPathCount (conjPrime₂ P).asIdeal P.asIdeal j i d f =
      decorationPathCount P.asIdeal P.asIdeal (n - j) i (decoratedNeighbourAtPrime (conjPrime₂ P) d) f := by
    unfold decorationPathCount
    congr 1
    ext e
    simp only [Finset.mem_filter, hPb]
    rw [heckeSet_conj_eq_topNeighbour P hne hST hSG hj d]
  rw [hL, hR]
  exact hsame i (n - j) (decoratedNeighbourAtPrime (conjPrime₂ P) d) f

end ConjDeco

end Formalism.L2.Col
