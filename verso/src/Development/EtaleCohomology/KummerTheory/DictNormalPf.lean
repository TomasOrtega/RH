import Development.EtaleCohomology.KummerTheory.DictPfEv

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def NrmMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
    Sec.res g (a p s h U x) = a p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def NrmDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (_hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
  (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
  ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
    m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U ((E.δ i).app (op U) x)

def up {X U : Scheme.{0}} {p q : ℕ} (x : Sx (sch.obj X) p U) : Sx (sch.obj X) q U := x

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) :
    ((sch.obj X).δ i).app (op U) x = up x := rfl

/- English proof (translation)
Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Finset.sum_range_succ, ih]`.

Break down `Nat.even_or_odd k with hk | hk` into its components or cases. Establish `: ¬ Even (k + 1)` using `by rw [Nat.even_add_one]; exact not_not.mpr hk`. Simplify using `[hk, this, hk.neg_one_pow]`. Establish `: Even (k + 1)` using `hk.add_one`. Establish `h2 : ¬ Even k` using `Nat.not_even_iff_odd.mpr hk`.

Simplify using `[h2, this, hk.neg_one_pow]`.
-/
theorem altsum (k : ℕ) : ∑ i : Fin k, (-1 : ℤ) ^ (i : ℕ) = if Even k then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hk
      simp [hk, this, hk.neg_one_pow]
    · have : Even (k + 1) := hk.add_one
      have h2 : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      simp [h2, this, hk.neg_one_pow]

/- English proof (translation)
Simplify using `[ev]`.
-/
theorem ev_zero' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} p s h U x :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, ev_add, ev_neg, ← sub_eq_add_neg]`.
-/
theorem ev_sub' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [sub_eq_add_neg, ev_add, ev_neg, ← sub_eq_add_neg]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

/- English proof (translation)
Introduce `R _ I X n α`. Establish `hα : δ n (n + 1) α.1 = 0` using `(Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2`. Take `⟨β, hβ⟩` from `hM R (E := sch.obj X) (I := I) (n := n - 1) (fun p s h U x => if Odd p then n.negOnePow • ev α.1 (p + 1) s (by push_cast; omega) U (up x) else 0) (by`. Introduce `p s h V U g x`. Simplify using `only`.

Use `split_ifs`. Rewrite using `[Units.smul_def, Units.smul_def]`. Use `(map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_` and prove the remaining obligations. Conclude with `congrArg (fun v => (n.negOnePow : ℤ) • v) (ev_res R α.1 (p + 1) s _ V U g (up x))`. Conclude with `map_zero _)`.

Set `γ : Cocycle ((chains R).obj (sch.obj X)) I n` to `⟨δ (n - 1) n β, (Cocycle.mem_iff n (n + 1) rfl _).2 (δ_δ _ _ _ _)⟩`. Use `⟨α - γ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff γ (n - 1) (by omega)]`. Conclude with `⟨β, rfl⟩`. Introduce `p s h U y show ev (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0`.

Rewrite using `[ev_sub', sub_eq_zero]`. Rewrite using `[hD R (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]`. Simplify using `only [face_sch, hβ]`. Break down `Nat.even_or_odd p with hp | hp` into its components or cases. Establish `hp1 : Odd (p + 1)` using `hp.add_one`.

Establish `hp0 : ¬ Odd p` using `Nat.not_odd_iff_even.mpr hp`. Simplify using `only [hp1, hp0, if_true, if_false, smul_zero, Finset.sum_const_zero, add_zero]`. Establish `hc` using `hD R (n := n) (m := n + 1) rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega) (by push_cast at h ⊢; omega) (up y)`. Rewrite `hc` using `[hα, ev_zero']`. Simplify using `only [face_sch] at hc`.

Rewrite `hc` using `[← Finset.sum_smul, altsum]`. Establish `he : ¬ Even (p + 1 + 2)`. Rewrite using `[Nat.not_even_iff_odd]`. Conclude with `hp1.add_even even_two`. Simplify using `only [he, if_false, one_smul] at hc`.

Rewrite `hc` using `[Int.negOnePow_succ, Units.neg_smul]`. Establish `key` using `add_neg_eq_zero.1 hc.symm`. Rewrite using `[Units.smul_def]`. Use `Eq.trans ?_ (map_zsmul ((I.d (s - 1) s).hom.app (op U)).hom _ _).symm` and prove the remaining obligations. Rewrite using `[show (ModuleCat.Hom.hom ((I.d (s - 1) s).hom.app (op U))) (ev α.1 (p + 1 + 1) (s - 1) (by push_cast at h ⊢; omega) U (up y)) = n.negOnePow • ev α.1 (p + 1) s (by push_cast at h ⊢; omega) U (up (up y)) from key]`.

Rewrite using `[← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]`. Both sides reduce to the same expression. Establish `hp1 : ¬ Odd (p + 1)` using `Nat.not_odd_iff_even.mpr hp.add_one`. Simplify using `only [hp1, hp, if_true, if_false, map_zero, zero_add]`. Rewrite using `[← Finset.sum_smul, altsum]`.

Establish `he : ¬ Even (p + 2)`. Rewrite using `[Nat.not_even_iff_odd]`. Conclude with `hp.add_even even_two`. Simplify using `only [he, if_false, one_smul, smul_smul, Int.units_mul_self]`. Both sides reduce to the same expression.
-/
theorem DictNormal_of (hM : NrmMk) (hD : NrmDelta) : DictNormal := by
  intro R _ I X n α
  have hα : δ n (n + 1) α.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2
  obtain ⟨β, hβ⟩ := hM R (E := sch.obj X) (I := I) (n := n - 1)
    (fun p s h U x => if Odd p then n.negOnePow • ev α.1 (p + 1) s (by push_cast; omega) U (up x) else 0)
    (by
      intro p s h V U g x
      dsimp only
      split_ifs
      · rw [Units.smul_def, Units.smul_def]
        refine (map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_
        exact congrArg (fun v => (n.negOnePow : ℤ) • v) (ev_res R α.1 (p + 1) s _ V U g (up x))
      · exact map_zero _)
  let γ : Cocycle ((chains R).obj (sch.obj X)) I n :=
    ⟨δ (n - 1) n β, (Cocycle.mem_iff n (n + 1) rfl _).2 (δ_δ _ _ _ _)⟩
  refine ⟨α - γ, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff γ (n - 1) (by omega)]
    exact ⟨β, rfl⟩
  · intro p s h U y
    show ev (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0
    rw [ev_sub', sub_eq_zero]
    rw [hD R (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]
    simp only [face_sch, hβ]
    rcases Nat.even_or_odd p with hp | hp
    ·
      have hp1 : Odd (p + 1) := hp.add_one
      have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
      simp only [hp1, hp0, if_true, if_false, smul_zero, Finset.sum_const_zero, add_zero]
      have hc := hD R (n := n) (m := n + 1) rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega)
        (by push_cast at h ⊢; omega) (up y)
      rw [hα, ev_zero'] at hc
      simp only [face_sch] at hc
      rw [← Finset.sum_smul, altsum] at hc
      have he : ¬ Even (p + 1 + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp1.add_even even_two
      simp only [he, if_false, one_smul] at hc
      rw [Int.negOnePow_succ, Units.neg_smul] at hc
      have key := add_neg_eq_zero.1 hc.symm
      rw [Units.smul_def]
      refine Eq.trans ?_ (map_zsmul ((I.d (s - 1) s).hom.app (op U)).hom _ _).symm
      rw [show (ModuleCat.Hom.hom ((I.d (s - 1) s).hom.app (op U))) (ev α.1 (p + 1 + 1) (s - 1) (by push_cast at h ⊢; omega) U (up y))
          = n.negOnePow • ev α.1 (p + 1) s (by push_cast at h ⊢; omega) U (up (up y)) from key]
      rw [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
      rfl
    · have hp1 : ¬ Odd (p + 1) := Nat.not_odd_iff_even.mpr hp.add_one
      simp only [hp1, hp, if_true, if_false, map_zero, zero_add]
      rw [← Finset.sum_smul, altsum]
      have he : ¬ Even (p + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp.add_even even_two
      simp only [he, if_false, one_smul, smul_smul, Int.units_mul_self]
      rfl

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

/- English proof (translation)
Simplify using `only [chainsXIso, chains, Functor.comp_obj]`. Use `erw [HomologicalComplex.extend_d_eq _ _ (i := p + 1) (j := p) rfl rfl]`. Use `erw [Iso.inv_hom_id_assoc]`. Use `congr 1`. Simplify using `only [chainsN, Functor.comp_obj]`.

Use `erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]`. Both sides reduce to the same expression.
-/
theorem chains_d (R : Type) [CommRing R] (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq _ _ (i := p + 1) (j := p) rfl rfl]
  erw [Iso.inv_hom_id_assoc]
  congr 1
  simp only [chainsN, Functor.comp_obj]
  erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  rfl

def evAt {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) : (F ⟶ G) →+ Sec G U where
  toFun φ := (φ.hom.app (op U)).hom y
  map_zero' := by simp
  map_add' := by simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evAt_apply {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) (φ : F ⟶ G) :
    evAt U y φ = (φ.hom.app (op U)).hom y := rfl

/- English proof (translation)
Introduce `R _ E I n m hm α U p s t hs ht x`. Unfold `ev`. Rewrite using `[δ_v n m hm α (-((p + 1 : ℕ) : ℤ)) t ht s (-(p : ℤ)) (by omega) (by push_cast; omega)]`. Rewrite using `[Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _), chains_d]`. Simplify using `only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]`.

Simplify using `[Units.smul_def, Finset.smul_sum]`. Use `(map_sum (evAt (G := I.X t) U (freeGen R (E.obj (op (SimplexCategory.mk (p + 1)))) U x)) _ _).trans ?_` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, map_zsmul]`. Use `congr 2`.

Use `free_gen_map R (E.δ i) U x` as an intermediate fact. Rewrite using `[evAt_apply]`. Simplify using the standard rewrite rules. Conclude with `congrArg (fun z => (ModuleCat.Hom.hom ((α.v (-(p : ℤ)) t (by push_cast at ht ⊢; omega)).hom.app (op U))) ((ModuleCat.Hom.hom ((chainsXIso R E p).inv.hom.app (op U))) z)) this`.
-/
theorem nrmDelta : NrmDelta := by
  intro R _ E I n m hm α U p s t hs ht x
  unfold ev
  rw [δ_v n m hm α (-((p + 1 : ℕ) : ℤ)) t ht s (-(p : ℤ)) (by omega) (by push_cast; omega)]
  rw [Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _),
    chains_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  simp [Units.smul_def, Finset.smul_sum]
  refine (map_sum (evAt (G := I.X t) U (freeGen R (E.obj (op (SimplexCategory.mk (p + 1)))) U x)) _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 2
  have := free_gen_map R (E.δ i) U x
  rw [evAt_apply]
  simp
  exact congrArg (fun z => (ModuleCat.Hom.hom ((α.v (-(p : ℤ)) t (by push_cast at ht ⊢; omega)).hom.app (op U)))
    ((ModuleCat.Hom.hom ((chainsXIso R E p).inv.hom.app (op U))) z)) this

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

/- English proof (translation)
The claim follows from `DictNormal_of hM nrmDelta`.
-/
theorem DictNormal_of' (hM : NrmMk) : DictNormal := DictNormal_of hM nrmDelta
end LateralTheory.KummerTheory
