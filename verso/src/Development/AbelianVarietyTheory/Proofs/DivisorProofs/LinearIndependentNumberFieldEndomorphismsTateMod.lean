import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPositiveDefiniteQuadraticFormEndomorphisms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleLevelComponentEqOfCardTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEndomorphismPowLevelComponentEqOneOfRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibleAlgClosureOfKillsTorsionSepClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdCoordsOfDefiniteParallelogramFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleCubicalLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfActsTriviallyAbelianVarietyAlgClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntExistsLevelNotDvdMulLiftStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CMFaithful

/- English proof (translation)
Introduce `K Ω _ _ _ _ A _ _ hA hd F _ _ O _ _ _ α l _ hl n a ha`. Take `⟨d, hd0, hdim⟩` from `hd`. Use `haveI : IsSepClosed Ω := IsSepClosure.sep_closed K`. Set `t` to `spMap (algebraMap K (AlgebraicClosure Ω))`. Set `B` to `(Over.pullback t).obj A`.

Set `β` to `OAct.pullback t A α`. Establish `hB : IsAbelianScheme B` using `GlobalTheory.isAbelianScheme_pullback_obj t A hA`. Use `haveI : IsCommMonObj B := hB.comm`. Take `⟨L, hL⟩` from `GlobalTheory.T.exists_symmetric_ample_cubical_lineBundle_abelianVariety (AlgebraicClosure Ω) B hB`. Take `⟨Q, hQ1, hQ2, hQ3, -⟩` from `GlobalTheory.SS.exists_quadraticForm_end (AlgebraicClosure Ω) B hB L hL`.

Set `ψ : O →+ Additive (B ⟶ B)` to `AddMonoidHom.mk' (fun x => Additive.ofMul (β.act x)) (fun x y => by rw [β.add]; rfl)`. Set `H : AddSubgroup (Additive (B ⟶ B))` to `{ carrier := {f | IsMonHom (Additive.toMul f)} add_mem' := fun {f g} hf hg => by`. Express the relevant statement in the definitionally equal form `IsMonHom (Additive.toMul f * Additive.toMul g)`. Use `haveI : IsMonHom (Additive.toMul f) := hf`. Use `haveI : IsMonHom (Additive.toMul g) := hg`.

Rewrite using `[Hom.mul_def]`. Use `infer_instance`. Use the proof step `zero_mem' := by`. Express the relevant statement in the definitionally equal form `IsMonHom (1 : B ⟶ B)`. Rewrite using `[Hom.one_def]`.

Use `infer_instance`. Use the proof step `neg_mem' := fun {f} hf => by`. Express the relevant statement in the definitionally equal form `IsMonHom (Additive.toMul f)⁻¹`. Use `haveI : IsMonHom (Additive.toMul f) := hf`. Use `infer_instance }`.

Establish `hu : ∀ i, ψ (a i) ∈ H` using `fun i => β.hom (a i)`. Establish `hinj : Function.Injective ψ` using `(injective_iff_map_eq_zero ψ).2 fun x hx => GlobalTheory.T.eq_zero_of_acts_trivially_abelianVariety_algClosure K Ω A hA ⟨d, hd0, hdim⟩ l hl F O α x (by`. Establish `: Additive.toMul (ψ x) = Additive.toMul 0` using `congrArg _ hx`. Conclude with `this)`. Establish `hindep : LinearIndependent ℤ (fun i => ψ (a i))`.

Establish `h1 : LinearIndependent ℤ (fun i => algebraMap O F (a i))` using `ha.restrict_scalars' ℤ`. Establish `h2 : LinearIndependent ℤ a`. Use `LinearIndependent.of_comp (algebraMap O F).toAddMonoidHom.toIntLinearMap ?_` and prove the remaining obligations. Conclude with `h1`. Conclude with `h2.map' ψ.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)`.

Take `⟨e, he, hE⟩` from `GlobalTheory.T.exists_dvd_coords_of_definite_parallelogram_form (Additive (B ⟶ B)) H (fun f => Q (Additive.toMul f)) (fun f g => by`. Use `hQ1 (Additive.toMul f) (Additive.toMul g)` as an intermediate fact. Simplify `this)` using `[div_eq_mul_inv]`. Use the proof step `(fun f => hQ2 _) (fun f hf h0 => by`. Use `hQ3 (Additive.toMul f) hf h0` as an intermediate fact.

Conclude with `this) n (fun i => ψ (a i)) hu hindep`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`.

Take `⟨j, hj⟩` from `hne`. Take `⟨N, hN⟩` from `GlobalTheory.T.padicInt_exists_level_not_dvd_mul_lift l (c j) hj e he`. Use `haveI : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Set `m : Fin n → ℤ` to `fun i => ((PadicInt.toZModPow N (c i)).val : ℤ)`. Establish `hm : ∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N))` using `fun i => by`.

Simplify using `[m]`. Set `φ : Fin n → ((ptOver K Ω ⟶ A) →* (ptOver K Ω ⟶ A))` to `fun i => actPts α.toRingAct (ptOver K Ω) (a i)`. Establish `kill` using `GlobalTheory.T.prod_endomorphism_pow_levelComponent_eq_one_of_relation (ptOver K Ω ⟶ A) l n φ c hc N m hm`. Set `x : O` to `∑ i, m i • a i`. Establish `hcomp : ∀ y : ptOver K Ω ⟶ A, y ≫ α.act x = ∏ i, (y ≫ α.act (a i)) ^ m i`.

Introduce `y`. Set `χ : O →+ Additive (ptOver K Ω ⟶ A)` to `AddMonoidHom.mk' (fun z => Additive.ofMul (y ≫ α.act z)) (fun z w => by rw [α.add, MonObj.comp_mul]; rfl)`. Establish `e1 : χ x = ∑ i, m i • χ (a i)` using `by simp only [x, map_sum, map_zsmul]`. Establish `e2` using `congrArg Additive.toMul e1`. Rewrite `e2` using `[toMul_sum]`.

Simplify using `only [toMul_zsmul] at e2`. Conclude with `e2`. Establish `hcard : ∀ k : ℕ, Nat.card {y : ptOver K Ω ⟶ A // y ^ (l ^ k) = 1} = l ^ (2 * d * k)` using `fun k => by`. Rewrite using `[GlobalTheory.T.card_abelianVariety_torsion_sepClosed K Ω A hA d hdim (l ^ k) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm k]`. Establish `hx : ∀ y : ptOver K Ω ⟶ A, y ^ (l ^ N) = 1 → y ≫ α.act x = 1`.

Introduce `y hy`. Take `⟨tt, rfl⟩` from `GlobalTheory.T.exists_tateModule_levelComponent_eq_of_card_torsion (ptOver K Ω ⟶ A) l (2 * d) hcard N y hy`. Rewrite using `[hcomp, ← kill tt]`. Both sides reduce to the same expression. Take `⟨h, hh, hfh⟩` from `GlobalTheory.T.divisible_algClosure_of_kills_torsion_sepClosed K Ω A hA (l ^ N) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl) (α.act x) (α.hom x) hx`.

Establish `hsum : (l ^ N) • Additive.ofMul h = ∑ i, m i • ψ (a i)`. Rewrite using `[← ofMul_pow, ← hfh]`. Express the relevant statement in the definitionally equal form `ψ x = _`. Simplify using `only [x, map_sum, map_zsmul]`. Use `hE (l ^ N) m (Additive.ofMul h) hh hsum j` as an intermediate fact.

Conclude with `hN (m j) (hm j) (by exact_mod_cast this)`.
-/
theorem linearIndependent_actTate : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (n : ℕ) (a : Fin n → O), LinearIndependent ℚ (fun i => algebraMap O F (a i)) → LinearIndependent ℤ_[l] (fun i => actTate α.toRingAct l (ptOver K Ω) (a i)) := by
  intro K Ω _ _ _ _ A _ _ hA hd F _ _ O _ _ _ α l _ hl n a ha
  obtain ⟨d, hd0, hdim⟩ := hd
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  let t := spMap (algebraMap K (AlgebraicClosure Ω))
  let B := (Over.pullback t).obj A
  let β := OAct.pullback t A α
  have hB : IsAbelianScheme B := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  haveI : IsCommMonObj B := hB.comm
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_symmetric_ample_cubical_lineBundle_abelianVariety (AlgebraicClosure Ω) B hB
  obtain ⟨Q, hQ1, hQ2, hQ3, -⟩ := GlobalTheory.SS.exists_quadraticForm_end (AlgebraicClosure Ω) B hB L hL
  let ψ : O →+ Additive (B ⟶ B) := AddMonoidHom.mk' (fun x => Additive.ofMul (β.act x))
    (fun x y => by rw [β.add]; rfl)
  let H : AddSubgroup (Additive (B ⟶ B)) :=
    { carrier := {f | IsMonHom (Additive.toMul f)}
      add_mem' := fun {f g} hf hg => by
        change IsMonHom (Additive.toMul f * Additive.toMul g)
        haveI : IsMonHom (Additive.toMul f) := hf
        haveI : IsMonHom (Additive.toMul g) := hg
        rw [Hom.mul_def]; infer_instance
      zero_mem' := by
        change IsMonHom (1 : B ⟶ B)
        rw [Hom.one_def]; infer_instance
      neg_mem' := fun {f} hf => by
        change IsMonHom (Additive.toMul f)⁻¹
        haveI : IsMonHom (Additive.toMul f) := hf
        infer_instance }
  have hu : ∀ i, ψ (a i) ∈ H := fun i => β.hom (a i)
  have hinj : Function.Injective ψ := (injective_iff_map_eq_zero ψ).2 fun x hx =>
    GlobalTheory.T.eq_zero_of_acts_trivially_abelianVariety_algClosure K Ω A hA ⟨d, hd0, hdim⟩ l hl F O α x (by
      have : Additive.toMul (ψ x) = Additive.toMul 0 := congrArg _ hx
      exact this)
  have hindep : LinearIndependent ℤ (fun i => ψ (a i)) := by
    have h1 : LinearIndependent ℤ (fun i => algebraMap O F (a i)) := ha.restrict_scalars' ℤ
    have h2 : LinearIndependent ℤ a := by
      refine LinearIndependent.of_comp (algebraMap O F).toAddMonoidHom.toIntLinearMap ?_
      exact h1
    exact h2.map' ψ.toIntLinearMap (LinearMap.ker_eq_bot.2 hinj)
  obtain ⟨e, he, hE⟩ := GlobalTheory.T.exists_dvd_coords_of_definite_parallelogram_form (Additive (B ⟶ B)) H (fun f => Q (Additive.toMul f))
    (fun f g => by
      have := hQ1 (Additive.toMul f) (Additive.toMul g)
      simpa [div_eq_mul_inv] using this)
    (fun f => hQ2 _) (fun f hf h0 => by
      have := hQ3 (Additive.toMul f) hf h0
      exact this) n (fun i => ψ (a i)) hu hindep
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push_neg at hne
  obtain ⟨j, hj⟩ := hne
  obtain ⟨N, hN⟩ := GlobalTheory.T.padicInt_exists_level_not_dvd_mul_lift l (c j) hj e he
  haveI : NeZero (l ^ N) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let m : Fin n → ℤ := fun i => ((PadicInt.toZModPow N (c i)).val : ℤ)
  have hm : ∀ i, PadicInt.toZModPow N (c i) = (m i : ZMod (l ^ N)) := fun i => by
    simp [m]
  let φ : Fin n → ((ptOver K Ω ⟶ A) →* (ptOver K Ω ⟶ A)) := fun i => actPts α.toRingAct (ptOver K Ω) (a i)
  have kill := GlobalTheory.T.prod_endomorphism_pow_levelComponent_eq_one_of_relation (ptOver K Ω ⟶ A) l n φ c hc N m hm
  let x : O := ∑ i, m i • a i
  have hcomp : ∀ y : ptOver K Ω ⟶ A, y ≫ α.act x = ∏ i, (y ≫ α.act (a i)) ^ m i := by
    intro y
    let χ : O →+ Additive (ptOver K Ω ⟶ A) := AddMonoidHom.mk' (fun z => Additive.ofMul (y ≫ α.act z))
      (fun z w => by rw [α.add, MonObj.comp_mul]; rfl)
    have e1 : χ x = ∑ i, m i • χ (a i) := by simp only [x, map_sum, map_zsmul]
    have e2 := congrArg Additive.toMul e1
    rw [toMul_sum] at e2
    simp only [toMul_zsmul] at e2
    exact e2
  have hcard : ∀ k : ℕ, Nat.card {y : ptOver K Ω ⟶ A // y ^ (l ^ k) = 1} = l ^ (2 * d * k) := fun k => by
    rw [GlobalTheory.T.card_abelianVariety_torsion_sepClosed K Ω A hA d hdim (l ^ k) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm k]
  have hx : ∀ y : ptOver K Ω ⟶ A, y ^ (l ^ N) = 1 → y ≫ α.act x = 1 := by
    intro y hy
    obtain ⟨tt, rfl⟩ := GlobalTheory.T.exists_tateModule_levelComponent_eq_of_card_torsion (ptOver K Ω ⟶ A) l (2 * d) hcard N y hy
    rw [hcomp, ← kill tt]
    rfl
  obtain ⟨h, hh, hfh⟩ := GlobalTheory.T.divisible_algClosure_of_kills_torsion_sepClosed K Ω A hA (l ^ N) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl) (α.act x) (α.hom x) hx
  have hsum : (l ^ N) • Additive.ofMul h = ∑ i, m i • ψ (a i) := by
    rw [← ofMul_pow, ← hfh]
    change ψ x = _
    simp only [x, map_sum, map_zsmul]
  have := hE (l ^ N) m (Additive.ofMul h) hh hsum j
  exact hN (m j) (hm j) (by exact_mod_cast this)

end GlobalTheory.CMFaithful
