import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.EtaDualPairing

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

open GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing in
/- English proof (translation)
Apply the tactic sequence `have key : ∀ b : DualNumber (O : Type), TrivSqZeroExt.fst b = 0 → b = (TrivSqZeroExt.inl (TrivSqZeroExt.snd b) : DualNumber (O : Type)) * DualNumber.eps := fun b hb => by ext <;> simp [hb]`. Conclude with `key x hx`.
-/
private theorem ker_red_eq {R₀ : Type} [CommRing R₀] (O : LAlg R₀) (x : (dual O : Type))
    (hx : (red O).1 x = 0) :
    x = (incl O).1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x) * eta O := by
  have key : ∀ b : DualNumber (O : Type), TrivSqZeroExt.fst b = 0 →
      b = (TrivSqZeroExt.inl (TrivSqZeroExt.snd b) : DualNumber (O : Type)) * DualNumber.eps :=
    fun b hb => by ext <;> simp [hb]
  exact key x hx

private def liftAlg {R₀ : Type} [CommRing R₀] {O R : Type} [CommRing O] [CommRing R] [Algebra R₀ O]
    [Algebra R₀ R] (s : O →ₐ[R₀] R) (i : R) (hi : i * i = 0) : DualNumber O →ₐ[R₀] R where
  toFun x := s x.fst + s x.snd * i
  map_one' := by simp
  map_mul' x y := by
    simp only [TrivSqZeroExt.fst_mul, DualNumber.snd_mul, map_mul, map_add]
    linear_combination (-(s x.snd * s y.snd)) * hi
  map_zero' := by simp
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]; ring
  commutes' r := by simp [TrivSqZeroExt.algebraMap_eq_inl']

open GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing in
/- English proof (translation)
Use `⟨⟨liftAlg s.1 i hi, ⟨fun x hx => ?_⟩⟩, Subtype.ext (AlgHom.ext fun x => ?_), ?_⟩` and prove the remaining obligations. Establish `hx' : IsUnit (s.1 (TrivSqZeroExt.fst (R` using `(O : Type)) (M := (O : Type)) x) + s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x) * i) := hx`. Establish `hn : IsNilpotent (-(s.1 (TrivSqZeroExt.snd (R` using `(O : Type)) (M := (O : Type)) x) * i)) := ⟨2, by linear_combination (s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x)) ^ 2 * hi⟩`. Establish `h2` using `hn.isUnit_add_left_of_commute hx' (Commute.all _ _)`. Rewrite `h2` using `[add_neg_cancel_right]`.

Conclude with `TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (s.2.map_nonunit _ h2)`. Express the relevant statement in the definitionally equal form `s.1 x + s.1 0 * i = s.1 x`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `s.1 0 + s.1 1 * i = i`. Simplify using the standard rewrite rules.
-/
private theorem exists_lift {R₀ : Type} [CommRing R₀] {O R : LAlg R₀} (s : LHom O R) (i : (R : Type))
    (hi : i * i = 0) : ∃ f : LHom (dual O) R, f.comp (incl O) = s ∧ f.1 (eta O) = i := by
  refine ⟨⟨liftAlg s.1 i hi, ⟨fun x hx => ?_⟩⟩, Subtype.ext (AlgHom.ext fun x => ?_), ?_⟩
  · have hx' : IsUnit (s.1 (TrivSqZeroExt.fst (R := (O : Type)) (M := (O : Type)) x) +
      s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x) * i) := hx
    have hn : IsNilpotent (-(s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x) * i)) :=
      ⟨2, by linear_combination (s.1 (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) x)) ^ 2 * hi⟩
    have h2 := hn.isUnit_add_left_of_commute hx' (Commute.all _ _)
    rw [add_neg_cancel_right] at h2
    exact TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (s.2.map_nonunit _ h2)
  · change s.1 x + s.1 0 * i = s.1 x
    simp
  · change s.1 0 + s.1 1 * i = i
    simp

/- English proof (translation)
Establish `hn : ∀ c : (R : Type), IsNilpotent (c * e)` using `fun c => ⟨2, by linear_combination c ^ 2 * he⟩`. Establish `key : ∀ (a b : Fin g → (R : Type)) (k : Fin g), nv s.1.toRingHom (F.F k) ![fun k => a k * e, fun k => b k * e] = (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (F.F k)) * a j + ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (F.F k)) * b j) * …`. Introduce `a b k`. Apply the tactic sequence `have h1 := (nv_calculus _ _ s.1.toRingHom 2 g ![fun k => a k * e, fun k => b k * e] (fun i j => by fin_cases i <;> exact hn _)).2.2.2.2.2 (fun i j i' j' => by`. Establish `: ∀ c d : (R : Type), c * e * (d * e) = 0` using `fun c d => by linear_combination c * d * he`.

Apply the tactic sequence `fin_cases i <;> fin_cases i' <;> exact this _ _) (F.F k)`. Rewrite using `[h1, F.const, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_two, add_mul, Finset.sum_mul, Finset.sum_mul]`. Simplify using `[_root_.mul_assoc]`. Establish `law : ∀ a b : Fin g → (R : Type), Y R s (fun k => a k * e) + Y R s (fun k => b k * e) = Y R s (fun k => (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (F.F k)) * a j + ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (F.F k)) * b j) * e)`. Introduce `a b`.

Rewrite using `[h.law R s _ _ (fun _ => hn _) (fun _ => hn _)]`. Simplify using `only [key]`. Establish `hz : Y R s (fun k => (0 : Fin g → (R : Type)) k * e) = 0`. Rewrite using `[← h.zero R s]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Establish `ha` using `law a 0`. Establish `hb` using `law 0 b`. Rewrite `ha` using `[hz, add_zero]`.

Rewrite `hb` using `[hz, zero_add]`. Establish `ha'` using `h.inj R s _ _ (fun _ => hn _) (fun _ => hn _) ha`. Establish `hb'` using `h.inj R s _ _ (fun _ => hn _) (fun _ => hn _) hb`. Rewrite using `[law]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Establish `h1` using `congrFun ha' k`. Establish `h2` using `congrFun hb' k`. Simplify using `only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at h1 h2`. Rewrite using `[add_mul, add_mul, ← h1, ← h2]`.
-/
private theorem chart_add {R₀ : Type} [CommRing R₀] {B : BX R₀} {O : LAlg R₀} {g : ℕ}
    {F : FGLaw (O : Type) g} {Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R}
    (h : BXChart B O F.F Y) (R : LAlg R₀) (s : LHom O R) (e : (R : Type)) (he : e * e = 0)
    (a b : Fin g → (R : Type)) :
    Y R s (fun k => a k * e) + Y R s (fun k => b k * e) = Y R s (fun k => (a k + b k) * e) := by
  have hn : ∀ c : (R : Type), IsNilpotent (c * e) := fun c => ⟨2, by linear_combination c ^ 2 * he⟩
  have key : ∀ (a b : Fin g → (R : Type)) (k : Fin g),
      nv s.1.toRingHom (F.F k) ![fun k => a k * e, fun k => b k * e] =
        (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (F.F k)) * a j +
          ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (F.F k)) * b j) * e := by
    intro a b k
    have h1 := (nv_calculus _ _ s.1.toRingHom 2 g ![fun k => a k * e, fun k => b k * e]
      (fun i j => by fin_cases i <;> exact hn _)).2.2.2.2.2 (fun i j i' j' => by
        have : ∀ c d : (R : Type), c * e * (d * e) = 0 := fun c d => by linear_combination c * d * he
        fin_cases i <;> fin_cases i' <;> exact this _ _) (F.F k)
    rw [h1, F.const, map_zero, zero_add, Fintype.sum_prod_type, Fin.sum_univ_two, add_mul,
      Finset.sum_mul, Finset.sum_mul]
    simp [_root_.mul_assoc]
  have law : ∀ a b : Fin g → (R : Type), Y R s (fun k => a k * e) + Y R s (fun k => b k * e) =
      Y R s (fun k => (∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (F.F k)) * a j +
          ∑ j, s.1 (MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (F.F k)) * b j) * e) := by
    intro a b
    rw [h.law R s _ _ (fun _ => hn _) (fun _ => hn _)]
    simp only [key]
  have hz : Y R s (fun k => (0 : Fin g → (R : Type)) k * e) = 0 := by
    rw [← h.zero R s]; congr 1; funext k; simp
  have ha := law a 0
  have hb := law 0 b
  rw [hz, add_zero] at ha
  rw [hz, zero_add] at hb
  have ha' := h.inj R s _ _ (fun _ => hn _) (fun _ => hn _) ha
  have hb' := h.inj R s _ _ (fun _ => hn _) (fun _ => hn _) hb
  rw [law]
  congr 1
  funext k
  have h1 := congrFun ha' k
  have h2 := congrFun hb' k
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, zero_add] at h1 h2
  rw [add_mul, add_mul, ← h1, ← h2]

open GlobalTheory.IndefiniteRowSideFullHecke.EtaDualPairing in

/- English proof (translation)
Introduce `R₀ _ B O g F Y h gb`. Establish `hee` using `eta_mul_eta O`. Establish `hn : ∀ c : (dual O : Type), IsNilpotent (c * eta O)` using `fun c => ⟨2, by linear_combination c ^ 2 * hee⟩`. Establish `hη : (red O).1 (eta O) = 0` using `rfl`. Establish `hex : ∀ l, ∃ a : Fin g → (dual O : Type), (∀ i, (red O).1 (a i) = 0) ∧ B.tg (red O) (red_sqZero O) (gb l ⊗ₜ[R₀] ⟨eta O, hη⟩) = Y (dual O) (incl O) a` using `fun l => h.surj (dual O) O (incl O) (red O) (incl O) (red_comp_incl O) (by rw [red_comp_incl]; rfl) (red_sqZero O) _ ((B.tg_ker _ _ _).2 ⟨_, rfl⟩)`.

Use `choose a ha0 ha using hex`. Set `S : Matrix (Fin g) (Fin g) (O : Type)` to `Matrix.of fun k l => TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) (a l k)`. Establish `haS : ∀ l, a l = fun k => (incl O).1 (S k l) * eta O` using `fun l =>`. Use function extensionality and compare the values at `fun k => ker_red_eq O _ (ha0 l k)`. Establish `hT : TanMat B O Y gb S`.

Introduce `R R' s π hπ l i`. Establish `hi : (i : (R : Type)) * i = 0`. Establish `: (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul i.2 i.2`.

Rewrite `this` using `[hπ.2, Ideal.mem_bot]`. Then use the resulting hypothesis. Take `⟨f, hf1, hf2⟩` from `exists_lift s (i : (R : Type)) hi`. Establish `hf : ∀ x ∈ (red O).ker, f.1.toLinearMap x ∈ π.ker` using `fun x hx => by`. Rewrite using `[ker_red_eq O x hx]`. Express the relevant statement in the definitionally equal form `π.1 (f.1 (_ * _)) = 0`.

Establish `hi0 : π.1 (i : (R : Type)) = 0` using `i.2`. Rewrite using `[map_mul, map_mul, hf2, hi0, mul_zero]`. Establish `h1` using `B.tg_nat (red O) π (red_sqZero O) hπ f hf (gb l ⊗ₜ[R₀] ⟨eta O, hη⟩)`. Rewrite `h1` using `[ha, haS, h.nat _ _ _ _ _ (fun _ => hn _), hf1, LinearMap.lTensor_tmul]`. Establish `h2 : (f.1.toLinearMap.restrict hf) ⟨eta O, hη⟩ = i` using `Subtype.ext hf2`.

Rewrite `h1` using `[h2]`. Rewrite using `[h1]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[map_mul, hf2, ← hf1]`.

Both sides reduce to the same expression. Use `⟨S, Matrix.mulVec_surjective_iff_isUnit.1 fun v => ?_, hT⟩` and prove the remaining obligations. Establish `hP : ∀ w, ∃ c : Fin g → (O : Type), B.tg (red O) (red_sqZero O) w = Y (dual O) (incl O) (fun k => (incl O).1 ((S *ᵥ c) k) * eta O)`. Set `P : B.G (dual O) → Prop` to `fun x => ∃ c : Fin g → (O : Type), x = Y (dual O) (incl O) (fun k => (incl O).1 ((S *ᵥ c) k) * eta O)`. Establish `P0 : P 0` using `⟨0, by rw [← h.zero (dual O) (incl O)]; congr 1; funext k; simp⟩`.

Establish `Padd : ∀ x y, P x → P y → P (x + y)`. Introduce and unpack `_ _ ⟨c, rfl⟩ ⟨c', rfl⟩`. Use `⟨c + c', ?_⟩` and prove the remaining obligations. Rewrite using `[chart_add h _ _ _ hee]`. Simplify using `only [Matrix.mulVec_add, Pi.add_apply, map_add]`.

Introduce `w`. Express the relevant statement in the definitionally equal form `P _`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `P0`.

Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Padd _ _ hx hy`. Consider the case `tmul m i`. Rewrite using `[← gb.sum_repr m, TensorProduct.sum_tmul, map_sum]`. Use `Finset.sum_induction _ P Padd P0 fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[TensorProduct.smul_tmul]`. Generalize the expression as in `(gb.repr m l) • i = j`. Use `⟨Pi.single l (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) j.1), ?_⟩` and prove the remaining obligations. Rewrite using `[hT]`. Use `congr 1`.

Use function extensionality and compare the values at `k`. Rewrite using `[Matrix.mulVec_single]`. Simplify using `only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.smul_apply, Matrix.col_apply, map_mul, _root_.mul_assoc]`. Rewrite using `[← ker_red_eq O j.1 j.2]`. Establish `hx : B.map (red O) (Y (dual O) (incl O) (fun k => (incl O).1 (v k) * eta O)) = 0`.

Rewrite using `[h.nat _ _ _ _ _ (fun _ => hn _), ← h.zero O ((red O).comp (incl O))]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[map_mul, hη, mul_zero]`. Both sides reduce to the same expression.

Take `⟨w, hw⟩` from `(B.tg_ker _ (red_sqZero O) _).1 hx`. Take `⟨c, hc⟩` from `hP w`. Establish `h3` using `h.inj _ _ _ _ (fun _ => hn _) (fun _ => hn _) (hc.symm.trans hw)`. Use `⟨c, funext fun k => ?_⟩` and prove the remaining obligations. Establish `h4` using `congrArg (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type))) (congrFun h3 k)`.

Establish `key : ∀ t : (O : Type), TrivSqZeroExt.snd (R` using `(O : Type)) (M := (O : Type)) ((incl O).1 t * eta O) = t := fun t => by`. Establish `: TrivSqZeroExt.snd ((TrivSqZeroExt.inl t : DualNumber (O : Type)) * (DualNumber.eps : DualNumber (O : Type))) = t` using `by simp`. Conclude with `this`. Rewrite `h4` using `[key, key]`. Then use the resulting hypothesis.
-/
theorem exists_tanMat : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ gb : Module.Basis (Fin g) R₀ B.gg, ∃ S : Matrix (Fin g) (Fin g) (O : Type), IsUnit S ∧ TanMat B O Y gb S := by
  intro R₀ _ B O g F Y h gb
  have hee := eta_mul_eta O
  have hn : ∀ c : (dual O : Type), IsNilpotent (c * eta O) :=
    fun c => ⟨2, by linear_combination c ^ 2 * hee⟩
  have hη : (red O).1 (eta O) = 0 := rfl
  have hex : ∀ l, ∃ a : Fin g → (dual O : Type), (∀ i, (red O).1 (a i) = 0) ∧
      B.tg (red O) (red_sqZero O) (gb l ⊗ₜ[R₀] ⟨eta O, hη⟩) = Y (dual O) (incl O) a := fun l =>
    h.surj (dual O) O (incl O) (red O) (incl O) (red_comp_incl O) (by rw [red_comp_incl]; rfl)
      (red_sqZero O) _ ((B.tg_ker _ _ _).2 ⟨_, rfl⟩)
  choose a ha0 ha using hex
  let S : Matrix (Fin g) (Fin g) (O : Type) :=
    Matrix.of fun k l => TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) (a l k)
  have haS : ∀ l, a l = fun k => (incl O).1 (S k l) * eta O := fun l =>
    funext fun k => ker_red_eq O _ (ha0 l k)
  have hT : TanMat B O Y gb S := by
    intro R R' s π hπ l i
    have hi : (i : (R : Type)) * i = 0 := by
      have : (i : (R : Type)) * i ∈ RingHom.ker π.1 ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul i.2 i.2
      rwa [hπ.2, Ideal.mem_bot] at this
    obtain ⟨f, hf1, hf2⟩ := exists_lift s (i : (R : Type)) hi
    have hf : ∀ x ∈ (red O).ker, f.1.toLinearMap x ∈ π.ker := fun x hx => by
      rw [ker_red_eq O x hx]
      change π.1 (f.1 (_ * _)) = 0
      have hi0 : π.1 (i : (R : Type)) = 0 := i.2
      rw [map_mul, map_mul, hf2, hi0, mul_zero]
    have h1 := B.tg_nat (red O) π (red_sqZero O) hπ f hf (gb l ⊗ₜ[R₀] ⟨eta O, hη⟩)
    rw [ha, haS, h.nat _ _ _ _ _ (fun _ => hn _), hf1, LinearMap.lTensor_tmul] at h1
    have h2 : (f.1.toLinearMap.restrict hf) ⟨eta O, hη⟩ = i := Subtype.ext hf2
    rw [h2] at h1
    rw [h1]
    congr 1
    funext k
    rw [map_mul, hf2, ← hf1]
    rfl
  refine ⟨S, Matrix.mulVec_surjective_iff_isUnit.1 fun v => ?_, hT⟩
  have hP : ∀ w, ∃ c : Fin g → (O : Type), B.tg (red O) (red_sqZero O) w =
      Y (dual O) (incl O) (fun k => (incl O).1 ((S *ᵥ c) k) * eta O) := by
    let P : B.G (dual O) → Prop := fun x => ∃ c : Fin g → (O : Type),
      x = Y (dual O) (incl O) (fun k => (incl O).1 ((S *ᵥ c) k) * eta O)
    have P0 : P 0 := ⟨0, by rw [← h.zero (dual O) (incl O)]; congr 1; funext k; simp⟩
    have Padd : ∀ x y, P x → P y → P (x + y) := by
      rintro _ _ ⟨c, rfl⟩ ⟨c', rfl⟩
      refine ⟨c + c', ?_⟩
      rw [chart_add h _ _ _ hee]
      simp only [Matrix.mulVec_add, Pi.add_apply, map_add]
    intro w
    change P _
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact P0
    | add x y hx hy => rw [map_add]; exact Padd _ _ hx hy
    | tmul m i =>
      rw [← gb.sum_repr m, TensorProduct.sum_tmul, map_sum]
      refine Finset.sum_induction _ P Padd P0 fun l _ => ?_
      rw [TensorProduct.smul_tmul]
      generalize (gb.repr m l) • i = j
      refine ⟨Pi.single l (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type)) j.1), ?_⟩
      rw [hT]
      congr 1
      funext k
      rw [Matrix.mulVec_single]
      simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, Pi.smul_apply, Matrix.col_apply,
        map_mul, _root_.mul_assoc]
      rw [← ker_red_eq O j.1 j.2]
  have hx : B.map (red O) (Y (dual O) (incl O) (fun k => (incl O).1 (v k) * eta O)) = 0 := by
    rw [h.nat _ _ _ _ _ (fun _ => hn _), ← h.zero O ((red O).comp (incl O))]
    congr 1
    funext k
    rw [map_mul, hη, mul_zero]; rfl
  obtain ⟨w, hw⟩ := (B.tg_ker _ (red_sqZero O) _).1 hx
  obtain ⟨c, hc⟩ := hP w
  have h3 := h.inj _ _ _ _ (fun _ => hn _) (fun _ => hn _) (hc.symm.trans hw)
  refine ⟨c, funext fun k => ?_⟩
  have h4 := congrArg (TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type))) (congrFun h3 k)
  have key : ∀ t : (O : Type), TrivSqZeroExt.snd (R := (O : Type)) (M := (O : Type))
      ((incl O).1 t * eta O) = t := fun t => by
    have : TrivSqZeroExt.snd ((TrivSqZeroExt.inl t : DualNumber (O : Type)) *
      (DualNumber.eps : DualNumber (O : Type))) = t := by simp
    exact this
  rwa [key, key] at h4

end GlobalTheory.ChF
