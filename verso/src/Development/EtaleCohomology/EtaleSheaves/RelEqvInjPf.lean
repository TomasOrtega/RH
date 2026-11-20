import Development.EtaleCohomology.EtaleSheaves.RelDescPf

noncomputable section
open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.RelEqvInjPf

set_option linter.unusedSectionVars false
variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

abbrev pl {K L : CochainComplex C ℤ} (f : K ⟶ L) (M : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass L M n →+ CohomologyClass K M n := cpre (Cocycle.ofHom f) M n n (zero_add n)

/- English proof (translation)
Simplify using `[mappingCone.map]`.
-/
lemma inr_map {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) : mappingCone.inr φ' ≫ mappingCone.map φ' φ α β comm = β ≫ mappingCone.inr φ := by
  simp [mappingCone.map]

/- English proof (translation)
Rewrite using `[mappingCone.ext_cochain_from_iff _ 0 1 (zero_add 1)]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_zero 1) (by omega)]`. Simplify using `[mappingCone.map]`. Rewrite using `[← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_map, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]`.

Simplify using the standard rewrite rules.
-/
lemma map_fst {A B A' B' : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) :
    (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp (mappingCone.fst φ).1 (zero_add 1) =
      (mappingCone.fst φ').1.comp (Cochain.ofHom α) (add_zero 1) := by
  rw [mappingCone.ext_cochain_from_iff _ 0 1 (zero_add 1)]
  constructor
  · rw [← Cochain.comp_assoc_of_second_is_zero_cochain, ← Cochain.comp_assoc _ _ _ (neg_add_cancel 1) (add_zero 1) (by omega)]
    simp [mappingCone.map]
  · rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_map, Cochain.ofHom_comp,
      Cochain.comp_assoc_of_first_is_zero_cochain]
    simp

/- English proof (translation)
Establish `h0 : pl α I k (CohomologyClass.mk z) = 0`. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp (Cocycle.ofHom α) z (zero_add k)) = 0`. Rewrite using `[CohomologyClass.mk_eq_zero_iff]`. Conclude with `⟨j, hjk, ξ, h⟩`. Establish `h1 : CohomologyClass.mk z = 0` using `hα (h0.trans (map_zero _).symm)`.

Rewrite `h1` using `[CohomologyClass.mk_eq_zero_iff]`. Take `⟨j', hj', t, ht⟩` from `h1`. Take `rfl : j' = j` from `by omega`. Conclude with `⟨t, ht⟩`.
-/
lemma laurent_adjoin_eq_of_image_eq {A' A I : CochainComplex C ℤ} (α : A' ⟶ A) {j k : ℤ} (hjk : j + 1 = k)
    (hα : Function.Injective (pl α I k)) (z : Cocycle A I k) (ξ : Cochain A' I j)
    (h : δ j k ξ = (Cochain.ofHom α).comp z.1 (zero_add k)) : ∃ t : Cochain A I j, δ j k t = z.1 := by
  have h0 : pl α I k (CohomologyClass.mk z) = 0 := by
    change CohomologyClass.mk (zcomp (Cocycle.ofHom α) z (zero_add k)) = 0
    rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨j, hjk, ξ, h⟩
  have h1 : CohomologyClass.mk z = 0 := hα (h0.trans (map_zero _).symm)
  rw [CohomologyClass.mk_eq_zero_iff] at h1
  obtain ⟨j', hj', t, ht⟩ := h1
  obtain rfl : j' = j := by omega
  exact ⟨t, ht⟩

/- English proof (translation)
Take `⟨W, hW⟩` from `hβ (CohomologyClass.mk z)`. Take `⟨w, rfl⟩` from `W.mk_surjective`. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp (Cocycle.ofHom β) w (zero_add k)) = _ at hW`. Establish `h2` using `hW.symm`. Rewrite `h2` using `[← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]`.

Take `⟨j', hj', r, hr⟩` from `h2`. Take `rfl : j' = j` from `by omega`. Conclude with `⟨w, r, by rw [hr]; rfl⟩`.
-/
lemma exists_finset_adjoin_laurent_preimage {B' B I : CochainComplex C ℤ} (β : B' ⟶ B) {j k : ℤ} (hjk : j + 1 = k)
    (hβ : Function.Surjective (pl β I k)) (z : Cocycle B' I k) :
    ∃ (w : Cocycle B I k) (r : Cochain B' I j), δ j k r = z.1 - (Cochain.ofHom β).comp w.1 (zero_add k) := by
  obtain ⟨W, hW⟩ := hβ (CohomologyClass.mk z)
  obtain ⟨w, rfl⟩ := W.mk_surjective
  change CohomologyClass.mk (zcomp (Cocycle.ofHom β) w (zero_add k)) = _ at hW
  have h2 := hW.symm
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff] at h2
  obtain ⟨j', hj', r, hr⟩ := h2
  obtain rfl : j' = j := by omega
  exact ⟨w, r, by rw [hr]; rfl⟩

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `y hy`. Take `⟨c, rfl⟩` from `y.mk_surjective`. Express the relevant statement in the definitionally equal form `CohomologyClass.mk (zcomp _ c _) = 0 at hy`. Rewrite `hy` using `[CohomologyClass.mk_eq_zero_iff]`.

Take `⟨m', hm', ξ0, hξ0⟩` from `hy`. Establish `em : m' = m` using `by omega`. Substitute `m'` using the available equality. Express the relevant statement in the definitionally equal form `δ m n ξ0 = (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp c.1 (zero_add n) at hξ0`. Use `set a := (mappingCone.inl φ).comp c.1 (show -1 + n = m by omega) with ha`.

Use `set b := (Cochain.ofHom (mappingCone.inr φ)).comp c.1 (zero_add n) with hb`. Establish `hdec : c.1 = mappingCone.descCochain φ a b hm`. Rewrite using `[mappingCone.ext_cochain_from_iff _ m n hm]`. Simplify using `[ha, hb]`. Establish `hc : δ n (n + 1) c.1 = 0` using `Cocycle.δ_eq_zero c (n + 1)`.

Rewrite `hc` using `[hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl]`. Establish `hδa : δ m n a = n.negOnePow • (Cochain.ofHom φ).comp b (zero_add n)`. Establish `h` using `congrArg (fun z => (mappingCone.inl φ).comp z (show -1 + (n + 1) = n by omega)) hc`. Simplify using `only [Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, Cochain.comp_zero, add_zero] at h`. Rewrite `h` using `[Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg, sub_eq_zero]`.

Conclude with `h`. Establish `hδb : δ n (n + 1) b = 0`. Establish `h` using `congrArg (fun z => (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add (n + 1))) hc`. Simplify using `using h`. Establish `h1 : δ m n ((Cochain.ofHom (mappingCone.inr φ')).comp ξ0 (zero_add m)) = (Cochain.ofHom β).comp (Cocycle.mk b (n + 1) rfl hδb).1 (zero_add n)`.

Rewrite using `[δ_ofHom_comp, hξ0, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_map, Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]`. Both sides reduce to the same expression. Take `⟨η, hη⟩` from `laurent_adjoin_eq_of_image_eq β hm hβi _ _ h1`. Express the relevant statement in the definitionally equal form `δ m n η = b at hη`. Use `set s := n.negOnePow with hs`.

Use `set γ := a - s • (Cochain.ofHom φ).comp η (zero_add m) with hγ`. Establish `hδγ : δ m n γ = 0`. Rewrite using `[hγ, δ_sub, δ_units_smul, δ_ofHom_comp, hη, hδa, sub_self]`. Use `set D0 := mappingCone.descCochain φ (0 : Cochain A I l) η hl with hD0`. Establish `hcγ : c.1 = δ m n D0 + (mappingCone.fst φ).1.comp γ (by omega)`.

Rewrite using `[hdec, hD0, mappingCone.δ_descCochain _ _ _ _ _ hm, hη, hγ]`. Simplify using `only [mappingCone.descCochain, δ_zero, zero_add, Cochain.comp_sub]`. Normalize the expressions using the abelian group laws. Use `set ξ := ξ0 - (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp D0 (zero_add m) with hξ`. Establish `h3 : δ m n ξ = (mappingCone.fst φ').1.comp ((Cochain.ofHom α).comp γ (zero_add m)) (by omega)`.

Rewrite using `[hξ, δ_sub, δ_ofHom_comp, hξ0, hcγ, Cochain.comp_add, add_sub_cancel_left, ← Cochain.comp_assoc_of_first_is_zero_cochain, map_fst, Cochain.comp_assoc_of_second_is_zero_cochain]`. Use `set p := (mappingCone.inl φ').comp ξ (show -1 + m = l by omega) with hp`. Use `set q := (Cochain.ofHom (mappingCone.inr φ')).comp ξ (zero_add m) with hq`. Establish `hdecξ : ξ = mappingCone.descCochain φ' p q hl`. Rewrite using `[mappingCone.ext_cochain_from_iff _ l m hl]`.

Simplify using `[hp, hq]`. Rewrite `h3` using `[hdecξ, mappingCone.δ_descCochain _ _ _ _ _ hm]`. Establish `h3a : δ l m p + s • (Cochain.ofHom φ').comp q (zero_add m) = (Cochain.ofHom α).comp γ (zero_add m)`. Establish `h` using `congrArg (fun z => (mappingCone.inl φ').comp z (show -1 + n = m by omega)) h3`. Simplify `h` using `only [Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, Cochain.comp_zero, add_zero]`.

Establish `h3b : δ m n q = 0`. Establish `h` using `congrArg (fun z => (Cochain.ofHom (mappingCone.inr φ')).comp z (zero_add n)) h3`. Simplify using `using h`. Take `⟨w, r, hr⟩` from `exists_finset_adjoin_laurent_preimage β hl hβs (Cocycle.mk q n hm h3b)`. Express the relevant statement in the definitionally equal form `δ l m r = q - (Cochain.ofHom β).comp w.1 (zero_add m) at hr`.

Establish `hw : δ m n w.1 = 0` using `Cocycle.δ_eq_zero w n`. Establish `h4 : δ l m (p + s • (Cochain.ofHom φ').comp r (zero_add l)) = (Cochain.ofHom α).comp (Cocycle.mk (γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m)) n hm (by rw [δ_sub, δ_units_smul, δ_ofHom_comp, hδγ, hw]; simp)).1 (zero_add m)`. Express the relevant statement in the definitionally equal form `_ = (Cochain.ofHom α).comp (γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m)) (zero_add m)`. Rewrite using `[δ_add, δ_units_smul, δ_ofHom_comp, hr, Cochain.comp_sub, Cochain.comp_sub, ← h3a, Cochain.comp_units_smul]`. Simplify using `only [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]`.

Rewrite using `[comm, smul_sub]`. Normalize the expressions using the abelian group laws. Take `⟨t, ht⟩` from `laurent_adjoin_eq_of_image_eq α hl hαi _ _ h4`. Express the relevant statement in the definitionally equal form `δ l m t = γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m) at ht`. Rewrite using `[CohomologyClass.mk_eq_zero_iff]`.

Use `⟨m, hm, D0 + mappingCone.descCochain φ t w.1 hl, ?_⟩` and prove the remaining obligations. Rewrite using `[δ_add, mappingCone.δ_descCochain φ t w.1 hl n hm, ht, hw, hcγ]`. Simplify using the standard rewrite rules. Rewrite using `[← hs, sub_add_cancel]`.
-/
theorem main {A B A' B' I : CochainComplex C ℤ} (φ : A ⟶ B) (φ' : A' ⟶ B') (α : A' ⟶ A) (β : B' ⟶ B)
    (comm : φ' ≫ β = α ≫ φ) (l m n : ℤ) (hl : l + 1 = m) (hm : m + 1 = n)
    (hαi : Function.Injective (pl α I m)) (hβi : Function.Injective (pl β I n))
    (hβs : Function.Surjective (pl β I m)) :
    Function.Injective (pl (mappingCone.map φ' φ α β comm) I n) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨c, rfl⟩ := y.mk_surjective
  change CohomologyClass.mk (zcomp _ c _) = 0 at hy
  rw [CohomologyClass.mk_eq_zero_iff] at hy
  obtain ⟨m', hm', ξ0, hξ0⟩ := hy
  have em : m' = m := by omega
  subst m'
  change δ m n ξ0 = (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp c.1 (zero_add n) at hξ0
  set a := (mappingCone.inl φ).comp c.1 (show -1 + n = m by omega) with ha
  set b := (Cochain.ofHom (mappingCone.inr φ)).comp c.1 (zero_add n) with hb
  have hdec : c.1 = mappingCone.descCochain φ a b hm := by
    rw [mappingCone.ext_cochain_from_iff _ m n hm]; simp [ha, hb]
  have hc : δ n (n + 1) c.1 = 0 := Cocycle.δ_eq_zero c (n + 1)
  rw [hdec, mappingCone.δ_descCochain _ _ _ _ _ rfl] at hc
  have hδa : δ m n a = n.negOnePow • (Cochain.ofHom φ).comp b (zero_add n) := by
    have h := congrArg (fun z => (mappingCone.inl φ).comp z (show -1 + (n + 1) = n by omega)) hc
    simp only [Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, Cochain.comp_zero,
      add_zero] at h
    rw [Int.negOnePow_succ, Units.neg_smul, ← sub_eq_add_neg, sub_eq_zero] at h
    exact h
  have hδb : δ n (n + 1) b = 0 := by
    have h := congrArg (fun z => (Cochain.ofHom (mappingCone.inr φ)).comp z (zero_add (n + 1))) hc
    simpa using h

  have h1 : δ m n ((Cochain.ofHom (mappingCone.inr φ')).comp ξ0 (zero_add m)) =
      (Cochain.ofHom β).comp (Cocycle.mk b (n + 1) rfl hδb).1 (zero_add n) := by
    rw [δ_ofHom_comp, hξ0, ← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp, inr_map,
      Cochain.ofHom_comp, Cochain.comp_assoc_of_first_is_zero_cochain]
    rfl
  obtain ⟨η, hη⟩ := laurent_adjoin_eq_of_image_eq β hm hβi _ _ h1
  change δ m n η = b at hη

  set s := n.negOnePow with hs
  set γ := a - s • (Cochain.ofHom φ).comp η (zero_add m) with hγ
  have hδγ : δ m n γ = 0 := by
    rw [hγ, δ_sub, δ_units_smul, δ_ofHom_comp, hη, hδa, sub_self]
  set D0 := mappingCone.descCochain φ (0 : Cochain A I l) η hl with hD0
  have hcγ : c.1 = δ m n D0 + (mappingCone.fst φ).1.comp γ (by omega) := by
    rw [hdec, hD0, mappingCone.δ_descCochain _ _ _ _ _ hm, hη, hγ]
    simp only [mappingCone.descCochain, δ_zero, zero_add, Cochain.comp_sub]
    abel

  set ξ := ξ0 - (Cochain.ofHom (mappingCone.map φ' φ α β comm)).comp D0 (zero_add m) with hξ
  have h3 : δ m n ξ = (mappingCone.fst φ').1.comp ((Cochain.ofHom α).comp γ (zero_add m)) (by omega) := by
    rw [hξ, δ_sub, δ_ofHom_comp, hξ0, hcγ, Cochain.comp_add, add_sub_cancel_left,
      ← Cochain.comp_assoc_of_first_is_zero_cochain, map_fst, Cochain.comp_assoc_of_second_is_zero_cochain]
  set p := (mappingCone.inl φ').comp ξ (show -1 + m = l by omega) with hp
  set q := (Cochain.ofHom (mappingCone.inr φ')).comp ξ (zero_add m) with hq
  have hdecξ : ξ = mappingCone.descCochain φ' p q hl := by
    rw [mappingCone.ext_cochain_from_iff _ l m hl]; simp [hp, hq]
  rw [hdecξ, mappingCone.δ_descCochain _ _ _ _ _ hm] at h3
  have h3a : δ l m p + s • (Cochain.ofHom φ').comp q (zero_add m) = (Cochain.ofHom α).comp γ (zero_add m) := by
    have h := congrArg (fun z => (mappingCone.inl φ').comp z (show -1 + n = m by omega)) h3
    simpa only [Cochain.comp_add, mappingCone.inl_fst_assoc, mappingCone.inl_snd_assoc, Cochain.comp_zero,
      add_zero] using h
  have h3b : δ m n q = 0 := by
    have h := congrArg (fun z => (Cochain.ofHom (mappingCone.inr φ')).comp z (zero_add n)) h3
    simpa using h

  obtain ⟨w, r, hr⟩ := exists_finset_adjoin_laurent_preimage β hl hβs (Cocycle.mk q n hm h3b)
  change δ l m r = q - (Cochain.ofHom β).comp w.1 (zero_add m) at hr
  have hw : δ m n w.1 = 0 := Cocycle.δ_eq_zero w n
  have h4 : δ l m (p + s • (Cochain.ofHom φ').comp r (zero_add l)) =
      (Cochain.ofHom α).comp (Cocycle.mk (γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m)) n hm
        (by rw [δ_sub, δ_units_smul, δ_ofHom_comp, hδγ, hw]; simp)).1 (zero_add m) := by
    change _ = (Cochain.ofHom α).comp (γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m)) (zero_add m)
    rw [δ_add, δ_units_smul, δ_ofHom_comp, hr, Cochain.comp_sub, Cochain.comp_sub, ← h3a,
      Cochain.comp_units_smul]
    simp only [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp]
    rw [comm, smul_sub]
    abel
  obtain ⟨t, ht⟩ := laurent_adjoin_eq_of_image_eq α hl hαi _ _ h4
  change δ l m t = γ - s • (Cochain.ofHom φ).comp w.1 (zero_add m) at ht

  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m, hm, D0 + mappingCone.descCochain φ t w.1 hl, ?_⟩
  rw [δ_add, mappingCone.δ_descCochain φ t w.1 hl n hm, ht, hw, hcγ]
  simp
  rw [← hs, sub_add_cancel]

/- English proof (translation)
Introduce `R _ F U E U' E' f f' u e comm hu he n`. Conclude with `main ((chains R).map f) ((chains R).map f') ((chains R).map u) ((chains R).map e) (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) (n - 1 - 1) (n - 1) n (by omega) (by omega) (hu (n - 1)).1 (he n).1 (he (n - 1)).2`.
-/
theorem RelEqvInj_of : LateralTheory.E.RelDescPf.RelEqvInj := by
  intro R _ F U E U' E' f f' u e comm hu he n
  exact main ((chains R).map f) ((chains R).map f') ((chains R).map u) ((chains R).map e)
    (by rw [← Functor.map_comp, ← Functor.map_comp, comm]) (n - 1 - 1) (n - 1) n (by omega) (by omega)
    (hu (n - 1)).1 (he n).1 (he (n - 1)).2

end LateralTheory.E.RelEqvInjPf
