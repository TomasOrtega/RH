import Development.EtaleCohomology.EtaleSheaves.FiltPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.TruncationPieces LateralTheory.E.FiltPf
open CochainComplex.HomComplex

namespace LateralTheory.E.TruncPf

def TruncBij : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) {K K' : Cx R} (g : K ⟶ K') (n : ℤ),
  (∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p)) → ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m)

def TruncData : Prop := ∀ (R : Type) [CommRing R] {K L : Cx R} (f : K ⟶ L) (n : ℤ),
  (∀ i : ℤ, 0 < i → IsZero (K.X i) ∧ IsZero (L.X i)) →
  ∃ (P : ℕ) (K' L' : Cx R) (f' : K' ⟶ L') (g : K ⟶ K') (h : L ⟶ L'),
    (∀ i : ℤ, (0 < i ∨ i < -(P : ℤ)) → IsZero (K'.X i) ∧ IsZero (L'.X i)) ∧ g ≫ f' = f ≫ h ∧
    (∀ p : ℤ, -(n + 1) ≤ p → IsIso (g.f p) ∧ IsIso (h.f p)) ∧
    (∀ p : ℤ, p < -(n + 1) → IsZero (K'.X p) ∧ IsZero (L'.X p))

variable (R : Type) [CommRing R] (F : Shv R)

/- English proof (translation)
Apply `CohomologyClass.homAddEquiv.injective` to reduce the goal to its premises. Simplify `h` using `only [CohomologyClass.homAddEquiv_apply]`.
-/
theorem toHom_inj {K : Cx R} (m : ℤ) {x y : HK R K F m}
    (h : CohomologyClass.toHom x = CohomologyClass.toHom y) : x = y := by
  apply CohomologyClass.homAddEquiv.injective
  simpa only [CohomologyClass.homAddEquiv_apply] using h

/- English proof (translation)
Apply `toHom_inj` to reduce the goal to its premises. Simplify using `only [LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom, Functor.map_comp, Category.assoc]`.
-/
theorem pull_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (m : ℤ) (x : HK R M F m) :
    HK.pull R (f ≫ g) F m x = HK.pull R f F m (HK.pull R g F m x) := by
  apply toHom_inj
  simp only [LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom, Functor.map_comp, Category.assoc]

/- English proof (translation)
Apply `toHom_inj` to reduce the goal to its premises. Rewrite using `[LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]`. Use `erw [CategoryTheory.Functor.map_id]`. Conclude with `Category.id_comp _`.
-/
theorem pull_id {K : Cx R} (m : ℤ) (x : HK R K F m) : HK.pull R (𝟙 K) F m x = x := by
  apply toHom_inj
  rw [LateralTheory.E.E8.ExciseCut.ConeZeroPf.pull_toHom]
  erw [CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/- English proof (translation)
Use `⟨fun x y hxy => ?_, fun y => ⟨HK.pull R (inv f) F m y, ?_⟩⟩` and prove the remaining obligations. Use `congrArg (HK.pull R (inv f) F m) hxy` as an intermediate fact. Simplify `this` using `only [← pull_comp, IsIso.inv_hom_id, pull_id]`. Rewrite using `[← pull_comp, IsIso.hom_inv_id, pull_id]`.
-/
theorem pull_bij_of_iso {K L : Cx R} (f : K ⟶ L) [IsIso f] (m : ℤ) : Function.Bijective (HK.pull R f F m) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨HK.pull R (inv f) F m y, ?_⟩⟩
  · have := congrArg (HK.pull R (inv f) F m) hxy
    simpa only [← pull_comp, IsIso.inv_hom_id, pull_id] using this
  · rw [← pull_comp, IsIso.hom_inv_id, pull_id]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y`. Apply `toHom_inj` to reduce the goal to its premises. Conclude with `(Functor.map_isZero (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)) hK).eq_of_src _ _`.
-/
theorem subsingleton_of_isZero {K : Cx R} (hK : IsZero K) (m : ℤ) : Subsingleton (HK R K F m) := by
  constructor
  intro x y
  apply toHom_inj
  exact (Functor.map_isZero (HomotopyCategory.quotient (Shv R) (ComplexShape.up ℤ)) hK).eq_of_src _ _

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun m _ _ => ⟨0, (subsingleton_of_isZero R F hK m).elim _ _⟩, fun _ _ _ => (subsingleton_of_isZero R F hL n).elim _ _⟩`.
-/
theorem relK_of_isZero {K L : Cx R} (f : K ⟶ L) (n : ℤ) (hK : IsZero K) (hL : IsZero L) : RelK R F n f :=
  ⟨fun m _ _ => ⟨0, (subsingleton_of_isZero R F hK m).elim _ _⟩,
    fun _ _ _ => (subsingleton_of_isZero R F hL n).elim _ _⟩

/- English proof (translation)
Establish `key : ∀ (m : ℤ) (z : HK R L' F m), HK.pull R f F m (HK.pull R h F m z) = HK.pull R g F m (HK.pull R f' F m z)`. Introduce `m z`. Rewrite using `[← pull_comp, ← pull_comp, w]`. Use `⟨fun m hm y => ?_, fun x1 x2 hx => ?_⟩` and prove the remaining obligations. Take `⟨y', rfl⟩` from `(hg m (by omega)).2 y`.

Take `⟨z, rfl⟩` from `hf'.1 m hm y'`. Conclude with `⟨_, key m z⟩`. Take `⟨w1, rfl⟩` from `(hh n le_rfl).2 x1`. Take `⟨w2, rfl⟩` from `(hh n le_rfl).2 x2`. Rewrite `hx` using `[key, key]`.

Rewrite using `[hf'.2 ((hg n le_rfl).1 hx)]`.
-/
theorem relK_of_square {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L') (g : K ⟶ K') (h : L ⟶ L')
    (w : g ≫ f' = f ≫ h) (n : ℤ)
    (hg : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R g F m))
    (hh : ∀ m : ℤ, m ≤ n → Function.Bijective (HK.pull R h F m))
    (hf' : RelK R F n f') : RelK R F n f := by
  have key : ∀ (m : ℤ) (z : HK R L' F m),
      HK.pull R f F m (HK.pull R h F m z) = HK.pull R g F m (HK.pull R f' F m z) := by
    intro m z
    rw [← pull_comp, ← pull_comp, w]
  refine ⟨fun m hm y => ?_, fun x1 x2 hx => ?_⟩
  · obtain ⟨y', rfl⟩ := (hg m (by omega)).2 y
    obtain ⟨z, rfl⟩ := hf'.1 m hm y'
    exact ⟨_, key m z⟩
  · obtain ⟨w1, rfl⟩ := (hh n le_rfl).2 x1
    obtain ⟨w2, rfl⟩ := (hh n le_rfl).2 x2
    rw [key, key] at hx
    rw [hf'.2 ((hg n le_rfl).1 hx)]

/- English proof (translation)
Use `relK_of_square R F (pieceC R f' p) (pieceC R f p) ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (inv (g.f _))) ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (inv (h.f _))) ?_ n (fun m _ => pull_bij_of_iso R F _ m) (fun m _ => pu …` and prove the remaining obligations. Simplify using `only [pieceC, ← Functor.map_comp]`. Use `congr 1`. Rewrite using `[IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]`. Use `congrArg (fun φ => HomologicalComplex.Hom.f φ (-(p : ℤ))) w` as an intermediate fact.

Simplify using `only [HomologicalComplex.comp_f] at this`. Conclude with `this.symm`.
-/
theorem piece_transfer {K L K' L' : Cx R} (f : K ⟶ L) (f' : K' ⟶ L') (g : K ⟶ K') (h : L ⟶ L')
    (w : g ≫ f' = f ≫ h) (n : ℤ) (p : ℕ) (hg : IsIso (g.f (-(p : ℤ)))) (hh : IsIso (h.f (-(p : ℤ))))
    (hp : RelK R F n (pieceC R f p)) : RelK R F n (pieceC R f' p) := by
  refine relK_of_square R F (pieceC R f' p) (pieceC R f p)
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (inv (g.f _)))
    ((HomologicalComplex.single (Shv R) (ComplexShape.up ℤ) (-(p : ℤ))).map (inv (h.f _))) ?_ n
    (fun m _ => pull_bij_of_iso R F _ m) (fun m _ => pull_bij_of_iso R F _ m) hp
  simp only [pieceC, ← Functor.map_comp]
  congr 1
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  have := congrArg (fun φ => HomologicalComplex.Hom.f φ (-(p : ℤ))) w
  simp only [HomologicalComplex.comp_f] at this
  exact this.symm

end LateralTheory.E.TruncPf

open LateralTheory.E.TruncPf in
/- English proof (translation)
Introduce `R _ F K L f n hz`. Take `⟨P, K', L', f', g, h, hb, w, hiso, hzero⟩` from `hD R f n hz`. Use `⟨P, K', L', f', hb, fun hp p => ?_, relK_of_square R F f f' g h w n (hB R F g n fun q hq => (hiso q hq).1) (hB R F h n fun q hq => (hiso q hq).2)⟩` and prove the remaining obligations. Distinguish the cases in `hq : -(n + 1) ≤ -(p : ℤ)`. Conclude with `piece_transfer R F f f' g h w n p (hiso _ hq).1 (hiso _ hq).2 (hp p)`.

Conclude with `relK_of_isZero R F _ n (Functor.map_isZero _ (hzero _ (by omega)).1) (Functor.map_isZero _ (hzero _ (by omega)).2)`.
-/
theorem LateralTheory.E.TruncPf.Trunc_of (hB : TruncBij) (hD : TruncData) : LateralTheory.E.FiltPf.Trunc := by
  intro R _ F K L f n hz
  obtain ⟨P, K', L', f', g, h, hb, w, hiso, hzero⟩ := hD R f n hz
  refine ⟨P, K', L', f', hb, fun hp p => ?_, relK_of_square R F f f' g h w n
    (hB R F g n fun q hq => (hiso q hq).1) (hB R F h n fun q hq => (hiso q hq).2)⟩
  by_cases hq : -(n + 1) ≤ -(p : ℤ)
  · exact piece_transfer R F f f' g h w n p (hiso _ hq).1 (hiso _ hq).2 (hp p)
  · exact relK_of_isZero R F _ n
      (Functor.map_isZero _ (hzero _ (by omega)).1) (Functor.map_isZero _ (hzero _ (by omega)).2)
