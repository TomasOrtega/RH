import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOfRetractGaloisFixedPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GaloisHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QkPointGaloisFixedUpToEquivDividedDataStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

/- English proof (translation)
Introduce `E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD`. Use `haveI : CharZero R := hR.2`. Establish `hadm : AdmBase R (maximalIdeal R)` using `hR.1`. Establish `hn : 1 ≤ l.M'` using `Nat.lcm_pos (by have := l.three_le; omega) l.A_pos`. Use `haveI := P.U.gen_hom`.

Use `GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed t.G t.G P.A P.U.gen (𝟙 _) (𝟙 _) l.M' P.U.gen_hom inferInstance inferInstance (Category.comp_id _) hn ?_` and prove the remaining obligations. Introduce `σ x hx`. Take `⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R` from `R) (AlgebraicClosure (FractionRing R))) ⟶ t.G, y = x := ⟨_, rfl⟩`. Take `⟨h, hh0⟩ : ∃ h : TFK (R` from `R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj t.G, h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩`. Establish `hy : y ^ l.M' = 1` using `by rw [hy0]; exact hx`.

Establish `hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp [Functor.map_one]`. Consider the case `succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]`.

Establish `hh : h ^ l.M' = 1`. Rewrite using `[hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]`. Take `⟨a, ha0⟩ : ∃ a : TFK (R` from `R) (AlgebraicClosure (FractionRing R)) ⟶ P.A.A, a = h ≫ P.U.gen.hom := ⟨_, rfl⟩`. Establish `ha : a ^ l.M' = 1`. Rewrite using `[ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]`.

Take `⟨f, hT, -⟩` from `GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U (AlgebraicClosure (FractionRing R)) l.M' hn`. Take `⟨p, hp⟩` from `hT.2.1 a ha`. Take `⟨⟨p', hext⟩, hpt, hiff⟩` from `GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom l.M' hn p`. Take `⟨a', ha'⟩` from `hpt a`. Establish `h2` using `(hiff p' a a' hext ha').1 ((hT.1 p a).2 hp.symm)`.

Establish `heq` using `GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data L R hR t P iw s ε e hε hs hD σ p p' hext`. Establish `haa : a' = a` using `((hT.1 p' a').1 h2).trans (((hT.2.2.1 p p').2 heq).symm.trans hp)`. Rewrite `ha'` using `[haa]`. Establish `e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h` using `by rw [Adjunction.homEquiv_unit, hh0]`. Establish `hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app t.G).left`.

Establish `e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app t.G` using `by conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]`. Conclude with `Adjunction.homEquiv_counit _ _ _ _`. Rewrite using `[e2, Over.comp_left]`. Both sides reduce to the same expression. Establish `hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left`.

Use `congrArg (· ≫ P.U.gen.inv.left) ha'` as an intermediate fact. Simplify using `only [ha0, Over.comp_left, Category.assoc] at this`. Rewrite `this` using `[← Over.comp_left _ _ _ P.U.gen.hom P.U.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id]`. Conclude with `this.symm`. Establish `hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left`.

Rewrite using `[hyl, ← Category.assoc, hhl]`. Rewrite `hyx` using `[hy0]`. Simplify using `using hyx`.
-/
theorem torsRat_of_divFrom : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (iw : L.W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ L.D.X) (e : P.D.toPre.X ≃ₗ[𝓞 E] L.D.X), (∀ k, ε k ∈ balForms H.bar L.D.X) → (∀ k, s k ≠ 0) → DivFrom L P.D.toPre P.oD iw s ε e → GlobalTheory.TChart.TorsRat t.G l.M' := by
  intro E _ _ _ H D' l c L R _ _ _ hR t P iw I _ s ε e hε hs hD
  haveI : CharZero R := hR.2
  have hadm : AdmBase R (maximalIdeal R) := hR.1
  have hn : 1 ≤ l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  haveI := P.U.gen_hom
  refine GlobalTheory.TorsDescent.torsRat_of_retract_galoisFixed t.G t.G P.A P.U.gen (𝟙 _) (𝟙 _) l.M' P.U.gen_hom
    inferInstance inferInstance (Category.comp_id _) hn ?_
  intro σ x hx
  obtain ⟨y, hy0⟩ : ∃ y : (Over.map (jK R)).obj (TFK (R := R) (AlgebraicClosure (FractionRing R))) ⟶ t.G, y = x := ⟨_, rfl⟩
  obtain ⟨h, hh0⟩ : ∃ h : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ (Over.pullback (jK R)).obj t.G,
    h = (Over.mapPullbackAdj (jK R)).unit.app _ ≫ (Over.pullback (jK R)).map y := ⟨_, rfl⟩
  have hy : y ^ l.M' = 1 := by rw [hy0]; exact hx
  have hmp : ∀ m : ℕ, (Over.pullback (jK R)).map (y ^ m) = ((Over.pullback (jK R)).map y) ^ m := by
    intro m
    induction m with
    | zero => simp [Functor.map_one]
    | succ m ih => rw [pow_succ, Functor.map_mul, ih, pow_succ]
  have hh : h ^ l.M' = 1 := by
    rw [hh0, ← MonObj.comp_pow, ← hmp, hy, Functor.map_one, MonObj.comp_one]
  obtain ⟨a, ha0⟩ : ∃ a : TFK (R := R) (AlgebraicClosure (FractionRing R)) ⟶ P.A.A, a = h ≫ P.U.gen.hom := ⟨_, rfl⟩
  have ha : a ^ l.M' = 1 := by
    rw [ha0, ← MonObj.pow_comp, hh, MonObj.one_comp]
  obtain ⟨f, hT, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) l.M' hn
  obtain ⟨p, hp⟩ := hT.2.1 a ha
  obtain ⟨⟨p', hext⟩, hpt, hiff⟩ := GlobalTheory.UT.Cl.galois_holds R (maximalIdeal R) hadm P.D P.A t.G t.semi P.U
    (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing R)) σ.toAlgHom l.M' hn p
  obtain ⟨a', ha'⟩ := hpt a
  have h2 := (hiff p' a a' hext ha').1 ((hT.1 p a).2 hp.symm)
  have heq := GlobalTheory.T.qkPoint_galois_fixed_up_to_equiv_divided_data L R hR t P iw s ε e hε hs hD σ p p' hext
  have haa : a' = a := ((hT.1 p' a').1 h2).trans (((hT.2.2.1 p p').2 heq).symm.trans hp)
  rw [haa] at ha'
  have e1 : (Over.mapPullbackAdj (jK R)).homEquiv _ _ y = h := by rw [Adjunction.homEquiv_unit, hh0]
  have hyl : y.left = h.left ≫ ((Over.mapPullbackAdj (jK R)).counit.app t.G).left := by
    have e2 : y = (Over.map (jK R)).map h ≫ (Over.mapPullbackAdj (jK R)).counit.app t.G := by
      conv_lhs => rw [← ((Over.mapPullbackAdj (jK R)).homEquiv _ _).symm_apply_apply y, e1]
      exact Adjunction.homEquiv_counit _ _ _ _
    rw [e2, Over.comp_left]
    rfl
  have hhl : spMap σ.toAlgHom.toRingHom ≫ h.left = h.left := by
    have := congrArg (· ≫ P.U.gen.inv.left) ha'
    simp only [ha0, Over.comp_left, Category.assoc] at this
    rw [← Over.comp_left _ _ _ P.U.gen.hom P.U.gen.inv, Iso.hom_inv_id, Over.id_left, Category.comp_id] at this
    exact this.symm
  have hyx : spMap σ.toAlgHom.toRingHom ≫ y.left = y.left := by
    rw [hyl, ← Category.assoc, hhl]
  rw [hy0] at hyx
  simpa using hyx

end GlobalTheory.UCanon
