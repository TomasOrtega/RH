import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.RadClKer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum

/- English proof (translation)
Establish `hQ : U ⊔ P ≤ A` using `sup_le hU hP`. Establish `hPQ : P.subgroupOf A ≤ (U ⊔ P).subgroupOf A` using `fun x hx => (le_sup_right : P ≤ U ⊔ P) hx`. Express the relevant statement in the definitionally equal form `(P.subgroupOf A).index = (P.subgroupOf U).index * _`. Rewrite using `[← Subgroup.relIndex_mul_index hPQ, Subgroup.relIndex_subgroupOf hQ, Subgroup.relIndex_sup_right, ← hf]`. Use `congr 1`.

Conclude with `Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv`.
-/
private theorem card_parity_sign_length_of_eq {G C : Type} [CommGroup G] [Group C] (A U P : Subgroup G) (hU : U ≤ A) (hP : P ≤ A)
    (f : A →* C) (hf : f.ker = (U ⊔ P).subgroupOf A) :
    Nat.card (A ⧸ P.subgroupOf A) = Nat.card (U ⧸ P.subgroupOf U) * Nat.card f.range := by
  have hQ : U ⊔ P ≤ A := sup_le hU hP
  have hPQ : P.subgroupOf A ≤ (U ⊔ P).subgroupOf A := fun x hx => (le_sup_right : P ≤ U ⊔ P) hx
  change (P.subgroupOf A).index = (P.subgroupOf U).index * _
  rw [← Subgroup.relIndex_mul_index hPQ, Subgroup.relIndex_subgroupOf hQ, Subgroup.relIndex_sup_right, ← hf]
  congr 1
  exact Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv

/- English proof (translation)
Introduce `K _ _ S n hn`. Take `⟨hmul, hpow, -⟩` from `radClMul K S n hn`. Set `f : SelK S n →* ClS S` to `MonoidHom.mk' (fun a => (QuotientGroup.mk (radCl n a.1) : ClS S)) fun a b => hmul a.1 a.2 b.1 b.2`. Establish `hU : S.unit K ≤ SelK S n`. Introduce `a ha v hv`.

Establish `h : v.valuation K (a : K) = 1` using `ha v hv`. Establish `h' : v.valuationOfNeZero a = 1`. Rewrite `h` using `[← HeightOneSpectrum.valuationOfNeZero_eq]`. Conclude with `h` after adjusting the coercions. Simplify using `[ordv, h']`.

Establish `hP : powK K n ≤ SelK S n`. Introduce and unpack `_ ⟨b, rfl⟩ v _`. Simplify using `[ordv]`. Establish `hf : f.ker = (S.unit K ⊔ powK K n).subgroupOf (SelK S n)`. Use extensionality with `a`.

Rewrite using `[MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← radClKer K S n hn a.1 a.2]`. Conclude with `QuotientGroup.eq_one_iff _`. Rewrite using `[card_parity_sign_length_of_eq _ _ _ hU hP f hf]`. Use `congr 1`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun c => ⟨?_, fun hc => ?_⟩)` and prove the remaining obligations.

Introduce and unpack `⟨a, rfl⟩`. Conclude with `hpow a.1 a.2`. Take `⟨a, ha, h⟩` from `radClSurj K S n hn c hc`. Conclude with `⟨⟨a, ha⟩, h⟩`.
-/
theorem UpperTheory.V.Kum.cardSel :
    ∀ (K : Type) [Field K] [NumberField K] (S : Set (HeightOneSpectrum (𝓞 K))) (n : ℕ), n ≠ 0 → Nat.card (SelK S n ⧸ (powK K n).subgroupOf (SelK S n)) = Nat.card (S.unit K ⧸ (powK K n).subgroupOf (S.unit K)) * Nat.card {c : ClS S // c ^ n = 1} := by
  intro K _ _ S n hn
  obtain ⟨hmul, hpow, -⟩ := radClMul K S n hn
  let f : SelK S n →* ClS S :=
    MonoidHom.mk' (fun a => (QuotientGroup.mk (radCl n a.1) : ClS S)) fun a b => hmul a.1 a.2 b.1 b.2
  have hU : S.unit K ≤ SelK S n := by
    intro a ha v hv
    have h : v.valuation K (a : K) = 1 := ha v hv
    have h' : v.valuationOfNeZero a = 1 := by
      rw [← HeightOneSpectrum.valuationOfNeZero_eq] at h
      exact_mod_cast h
    simp [ordv, h']
  have hP : powK K n ≤ SelK S n := by
    rintro _ ⟨b, rfl⟩ v _
    simp [ordv]
  have hf : f.ker = (S.unit K ⊔ powK K n).subgroupOf (SelK S n) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← radClKer K S n hn a.1 a.2]
    exact QuotientGroup.eq_one_iff _
  rw [card_parity_sign_length_of_eq _ _ _ hU hP f hf]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ⟨?_, fun hc => ?_⟩)
  · rintro ⟨a, rfl⟩
    exact hpow a.1 a.2
  · obtain ⟨a, ha, h⟩ := radClSurj K S n hn c hc
    exact ⟨⟨a, ha⟩, h⟩
