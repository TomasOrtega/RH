import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyPresheafClassesAsCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.LeraySurj

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `h2 : ((chainsN R).obj E).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)` using `AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _`. Rewrite using `[← h2]`. Conclude with `HomologicalComplex.extend_d_eq _ _ rfl rfl`.
-/
theorem chains_d_eq (E : Spc) (n : ℕ) :
    ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (chainsXIso R E (n + 1)).hom ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫
        (chainsXIso R E n).inv := by
  have h2 : ((chainsN R).obj E).d (n + 1) n = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
    AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ _
  rw [← h2]
  exact HomologicalComplex.extend_d_eq _ _ rfl rfl

/- English proof (translation)
Rewrite using `[chains_d_eq]`. Simplify using `only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, Preadditive.sum_comp, Preadditive.zsmul_comp]`. Both sides reduce to the same expression.
-/
theorem cobd_eq (E : Spc) {F : Shv R} (n : ℕ) (s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) :
    cobd s = (chainsXIso R E (n + 1)).inv ≫ ((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (chainsXIso R E n).hom ≫ s := by
  rw [chains_d_eq]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, Preadditive.sum_comp, Preadditive.zsmul_comp]
  rfl

/- English proof (translation)
Establish `hcl : z.1.v (-(k : ℤ)) (n - k) (by omega) ≫ (res R F).d (n - k) (n - k + 1) = 0`. Establish `h` using `Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) (-(k : ℤ)) (n - k + 1) (by omega)`. Rewrite `h` using `[δ_v n (n + 1) rfl _ _ _ _ (n - k) (-(k : ℤ) + 1) (by omega) rfl, hv (-(k : ℤ) + 1) _ _ (by omega)]`. Simplify using `using h`. Take `⟨y, hy⟩` from `hex ((chainsXIso R E k).inv ≫ z.1.v (-(k : ℤ)) (n - k) (by omega)) (by rw [Category.assoc, hcl, Limits.comp_zero])`.

Set `β : Cochain ((chains R).obj E) (res R F) (n - 1)` to `Cochain.single (p := -(k : ℤ)) (q := n - k - 1) ((chainsXIso R E k).hom ≫ y) (n - 1)`. Set `c : Cocycle ((chains R).obj E) (res R F) n` to `Cocycle.mk (δ (n - 1) n β) (n + 1) (by omega) (δ_δ _ _ _ _)`. Use `⟨z - c, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]`. Conclude with `⟨β, rfl⟩`.

Introduce `p q hpq hp`. Establish `hβ1 : β.v (p + 1) q (by omega) = 0` using `Cochain.single_v_eq_zero _ _ _ _ _ (by omega)`. Establish `hc : c.1.v p q hpq = β.v p (q - 1) (by omega) ≫ (res R F).d (q - 1) q`. Express the relevant statement in the definitionally equal form `(δ (n - 1) n β).v p q hpq = _`. Rewrite using `[δ_v (n - 1) n (by omega) _ _ _ _ (q - 1) (p + 1) rfl rfl, hβ1]`.

Simplify using the standard rewrite rules. Rewrite using `[Cocycle.coe_sub, Cochain.sub_v, hc]`. Break down `lt_or_eq_of_le (show -(k : ℤ) ≤ p by omega) with h | h` into its components or cases. Rewrite using `[hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]`. Simplify using the standard rewrite rules.

Substitute `h` using the available equality. Take `rfl : q = n - k` from `by omega`. Rewrite using `[Cochain.single_v]`. Establish `hz : z.1.v (-(k : ℤ)) (n - k) hpq = (chainsXIso R E k).hom ≫ ((chainsXIso R E k).inv ≫ z.1.v (-(k : ℤ)) (n - k) hpq)`. Rewrite using `[Iso.hom_inv_id_assoc]`.

Rewrite using `[hz, hy]`. Simplify using the standard rewrite rules.
-/
theorem step (E : Spc) (F : Shv R) {n : ℤ} (z : Cocycle ((chains R).obj E) (res R F) n) (k : ℕ)
    (hv : ∀ p q (hpq : p + n = q), -(k : ℤ) < p → z.1.v p q hpq = 0)
    (hex : ∀ t : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X (n - k), t ≫ (res R F).d (n - k) (n - k + 1) = 0 →
      ∃ y : (free R).obj (E.obj (op ⦋k⦌)) ⟶ (res R F).X (n - k - 1), t = y ≫ (res R F).d (n - k - 1) (n - k)) :
    ∃ z' : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z' = CohomologyClass.mk z ∧
      ∀ p q (hpq : p + n = q), -((k + 1 : ℕ) : ℤ) < p → z'.1.v p q hpq = 0 := by
  have hcl : z.1.v (-(k : ℤ)) (n - k) (by omega) ≫ (res R F).d (n - k) (n - k + 1) = 0 := by
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z (n + 1)) (-(k : ℤ)) (n - k + 1) (by omega)
    rw [δ_v n (n + 1) rfl _ _ _ _ (n - k) (-(k : ℤ) + 1) (by omega) rfl,
      hv (-(k : ℤ) + 1) _ _ (by omega)] at h
    simpa using h
  obtain ⟨y, hy⟩ := hex ((chainsXIso R E k).inv ≫ z.1.v (-(k : ℤ)) (n - k) (by omega))
    (by rw [Category.assoc, hcl, Limits.comp_zero])
  let β : Cochain ((chains R).obj E) (res R F) (n - 1) :=
    Cochain.single (p := -(k : ℤ)) (q := n - k - 1) ((chainsXIso R E k).hom ≫ y) (n - 1)
  let c : Cocycle ((chains R).obj E) (res R F) n := Cocycle.mk (δ (n - 1) n β) (n + 1) (by omega) (δ_δ _ _ _ _)
  refine ⟨z - c, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨β, rfl⟩
  · intro p q hpq hp
    have hβ1 : β.v (p + 1) q (by omega) = 0 := Cochain.single_v_eq_zero _ _ _ _ _ (by omega)
    have hc : c.1.v p q hpq = β.v p (q - 1) (by omega) ≫ (res R F).d (q - 1) q := by
      change (δ (n - 1) n β).v p q hpq = _
      rw [δ_v (n - 1) n (by omega) _ _ _ _ (q - 1) (p + 1) rfl rfl, hβ1]
      simp
    rw [Cocycle.coe_sub, Cochain.sub_v, hc]
    rcases lt_or_eq_of_le (show -(k : ℤ) ≤ p by omega) with h | h
    · rw [hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]
      simp
    · subst h
      obtain rfl : q = n - k := by omega
      rw [Cochain.single_v]
      have hz : z.1.v (-(k : ℤ)) (n - k) hpq = (chainsXIso R E k).hom ≫ ((chainsXIso R E k).inv ≫ z.1.v (-(k : ℤ)) (n - k) hpq) := by
        rw [Iso.hom_inv_id_assoc]
      rw [hz, hy]
      simp

/- English proof (translation)
Take `⟨cl, -, hinj, hzero, -⟩` from `GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F`. Establish `h : cl P m t ht = cl P m 0 Limits.zero_comp` using `by rw [hzero]; exact h0 _`. Take `⟨y, hy⟩` from `(hinj P m t ht 0 Limits.zero_comp).1 h`. Conclude with `⟨y, by rw [hy, zero_add]⟩`.
-/
theorem exact_of_vanish (F : Shv R) (P : PSh) (m : ℤ) (h0 : ∀ y : H R (disc.obj P) F m, y = 0)
    (t : (free R).obj P ⟶ (res R F).X m) (ht : t ≫ (res R F).d m (m + 1) = 0) :
    ∃ y : (free R).obj P ⟶ (res R F).X (m - 1), t = y ≫ (res R F).d (m - 1) m := by
  obtain ⟨cl, -, hinj, hzero, -⟩ := GlobalTheory.T.etaleSpaceCohomology_presheaf_classes_as_cocycles R F
  have h : cl P m t ht = cl P m 0 Limits.zero_comp := by rw [hzero]; exact h0 _
  obtain ⟨y, hy⟩ := (hinj P m t ht 0 Limits.zero_comp).1 h
  exact ⟨y, by rw [hy, zero_add]⟩

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero`. Take `⟨z, rfl⟩` from `x.mk_surjective`. Use `⟨z, rfl, fun p q hpq hp => ?_⟩` and prove the remaining obligations. Conclude with `((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F).2.2.2.2.2 E p (by omega)).eq_of_src _ _`.

Consider the case `succ j ih`. Take `⟨z, hz, hv⟩` from `ih (by omega)`. Take `⟨z', hz', hv'⟩` from `step E F z j hv (fun t ht => by`. Establish `hm : ((n - j : ℕ) : ℤ) = (n : ℤ) - j` using `by omega`. Establish `h0` using `hyp j (n - j) (by omega) (by omega)`.

Rewrite `h0` using `[hm]`. Use `exact_of_vanish F _ ((n : ℤ) - j) h0 t ht` as an intermediate fact. Conclude with `this)`. Conclude with `⟨z', hz'.trans hz, hv'⟩`.
-/
theorem reduce (F : Shv R) (E : Spc) (n : ℕ)
    (hyp : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (x : H R E F n) (j : ℕ) (hj : j ≤ n) :
    ∃ z : Cocycle ((chains R).obj E) (res R F) n, CohomologyClass.mk z = x ∧
      ∀ (p q : ℤ) (hpq : p + n = q), -(j : ℤ) < p → z.1.v p q hpq = 0 := by
  induction j with
  | zero =>
    obtain ⟨z, rfl⟩ := x.mk_surjective
    refine ⟨z, rfl, fun p q hpq hp => ?_⟩
    exact ((GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F).2.2.2.2.2 E p (by omega)).eq_of_src _ _
  | succ j ih =>
    obtain ⟨z, hz, hv⟩ := ih (by omega)
    obtain ⟨z', hz', hv'⟩ := step E F z j hv (fun t ht => by
      have hm : ((n - j : ℕ) : ℤ) = (n : ℤ) - j := by omega
      have h0 := hyp j (n - j) (by omega) (by omega)
      rw [hm] at h0
      have := exact_of_vanish F _ ((n : ℤ) - j) h0 t ht
      exact this)
    exact ⟨z', hz'.trans hz, hv'⟩

/- English proof (translation)
Take `⟨z, rfl, hv⟩` from `reduce F E n hyp x n le_rfl`. Take `⟨-, hneg, hmono, ⟨w, hex⟩, -, -⟩` from `GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F`. Establish `hcl : z.1.v (-(n : ℤ)) 0 (by omega) ≫ (res R F).d 0 1 = 0`. Establish `h` using `Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-(n : ℤ)) 1 (by omega)`. Rewrite `h` using `[δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ 0 (-(n : ℤ) + 1) (by omega) rfl, hv (-(n : ℤ) + 1) _ _ (by omega)]`.

Simplify using `using h`. Take `⟨u, hu⟩` from `hex.lift' ((chainsXIso R E n).inv ≫ z.1.v (-(n : ℤ)) 0 (by omega)) (by change _ ≫ (res R F).d 0 1 = 0; rw [Category.assoc, hcl, Limits.comp_zero])`. Express the relevant statement in the definitionally equal form `u ≫ resι R F = _ at hu`. Establish `hz : z.1.v (-(n : ℤ)) 0 (by omega) = (chainsXIso R E n).hom ≫ u ≫ resι R F`. Rewrite using `[hu, Iso.hom_inv_id_assoc]`.

Use `⟨u, ?_, z, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[cobd_eq]`. Establish `h` using `Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((n + 1 : ℕ) : ℤ)) 0 (by omega)`. Rewrite `h` using `[δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ (-1) (-(n : ℤ)) (by omega) (by omega), hz, (hneg (-1) (by omega)).eq_of_tgt (z.1.v _ (-1) _) 0]`. Simplify using `only [Limits.zero_comp, zero_add, Cochain.zero_v] at h`.

Establish `h'` using `(smul_eq_zero_iff_eq _).1 h`. Establish `h'' : (((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (chainsXIso R E n).hom ≫ u) ≫ resι R F = 0 ≫ resι R F`. Simplify `h'` using `[Category.assoc]`. Rewrite `h''` using `[cancel_mono]`. Rewrite using `[h'', Limits.comp_zero]`.

Use `Cochain.ext _ _ (fun p q hpq => ?_)` and prove the remaining obligations. Break down `lt_trichotomy p (-(n : ℤ)) with h | h | h` into its components or cases. Conclude with `(hneg q (by omega)).eq_of_tgt _ _`. Substitute `h` using the available equality. Take `rfl : q = 0` from `by omega`.

Rewrite using `[Cochain.single_v, hz]`. Rewrite using `[hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]`.
-/
theorem main (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ)
    (hyp : ∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0)
    (x : H R E F n) : ∃ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 ∧ IsCls s x := by
  obtain ⟨z, rfl, hv⟩ := reduce F E n hyp x n le_rfl
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, -⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  have hcl : z.1.v (-(n : ℤ)) 0 (by omega) ≫ (res R F).d 0 1 = 0 := by
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-(n : ℤ)) 1 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ 0 (-(n : ℤ) + 1) (by omega) rfl,
      hv (-(n : ℤ) + 1) _ _ (by omega)] at h
    simpa using h
  obtain ⟨u, hu⟩ := hex.lift' ((chainsXIso R E n).inv ≫ z.1.v (-(n : ℤ)) 0 (by omega))
    (by change _ ≫ (res R F).d 0 1 = 0; rw [Category.assoc, hcl, Limits.comp_zero])
  change u ≫ resι R F = _ at hu
  have hz : z.1.v (-(n : ℤ)) 0 (by omega) = (chainsXIso R E n).hom ≫ u ≫ resι R F := by
    rw [hu, Iso.hom_inv_id_assoc]
  refine ⟨u, ?_, z, rfl, ?_⟩
  · rw [cobd_eq]
    have h := Cochain.congr_v (Cocycle.δ_eq_zero z ((n : ℤ) + 1)) (-((n + 1 : ℕ) : ℤ)) 0 (by omega)
    rw [δ_v (n : ℤ) ((n : ℤ) + 1) rfl _ _ _ _ (-1) (-(n : ℤ)) (by omega) (by omega), hz,
      (hneg (-1) (by omega)).eq_of_tgt (z.1.v _ (-1) _) 0] at h
    simp only [Limits.zero_comp, zero_add, Cochain.zero_v] at h
    have h' := (smul_eq_zero_iff_eq _).1 h
    have h'' : (((chains R).obj E).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫ (chainsXIso R E n).hom ≫ u) ≫ resι R F =
        0 ≫ resι R F := by
      simpa [Category.assoc] using h'
    rw [cancel_mono] at h''
    rw [h'', Limits.comp_zero]
  · refine Cochain.ext _ _ (fun p q hpq => ?_)
    rcases lt_trichotomy p (-(n : ℤ)) with h | h | h
    · exact (hneg q (by omega)).eq_of_tgt _ _
    · subst h
      obtain rfl : q = 0 := by omega
      rw [Cochain.single_v, hz]
    · rw [hv p q hpq h, Cochain.single_v_eq_zero _ _ _ _ _ (by omega)]

end GlobalTheory.EtC.LeraySurj

/- English proof (translation)
Introduce `R _ F E n hyp x` and use `GlobalTheory.EtC.LeraySurj.main R F E n hyp x`.
-/
theorem GlobalTheory.EtC.leray_surj : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (n : ℕ), (∀ k m : ℕ, 0 < m → k + m = n → ∀ y : H R (disc.obj (E.obj (op ⦋k⦌))) F m, y = 0) → ∀ x : H R E F n, ∃ s : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F, cobd s = 0 ∧ IsCls s x :=
  fun R _ F E n hyp x => GlobalTheory.EtC.LeraySurj.main R F E n hyp x
