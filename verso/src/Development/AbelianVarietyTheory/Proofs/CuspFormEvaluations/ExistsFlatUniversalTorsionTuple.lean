import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace TorsTuple

/- English proof (translation)
Establish `key : ∀ n : ℕ, ∃ (R : Over X) (p : Fin n → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧ ∀ (T : Over X) (u : Fin n → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Use `⟨Over.mk (𝟙 X), fun i => i.elim0, ?_, ?_, fun T u => ⟨Over.homMk T.hom (by simp), fun i => i.elim0⟩⟩` and prove the remaining obligations.

Use `show IsAffineHom (𝟙 X) infer_instance`. Use `show Flat (𝟙 X) infer_instance`. Consider the case `succ n ih`. Take `⟨R, p, hRa, hRf, hR⟩` from `ih`. Establish `ha : IsAffineHom (pullback.fst R.hom Q.hom)` using `MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom) (IsPullback.of_hasPullback R.hom Q.hom).flip ‹_›`.

Set `R' : Over X` to `Over.mk (pullback.fst R.hom Q.hom ≫ R.hom)`. Set `a : R' ⟶ Q` to `Over.homMk (pullback.snd R.hom Q.hom) pullback.condition.symm`. Set `b : R' ⟶ R` to `Over.homMk (pullback.fst R.hom Q.hom) rfl`. Use `⟨R', Fin.cons (α := fun _ => R' ⟶ Q) a (fun i => b ≫ p i), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show IsAffineHom (pullback.fst R.hom Q.hom ≫ R.hom) infer_instance`.

Use `show Flat (pullback.fst R.hom Q.hom ≫ R.hom) infer_instance`. Introduce `T u`. Take `⟨v, hv⟩` from `hR T (fun i => u i.succ)`. Establish `hc : v.left ≫ R.hom = (u 0).left ≫ Q.hom` using `by rw [Over.w v, Over.w (u 0)]`. Use `⟨Over.homMk (pullback.lift v.left (u 0).left hc) (by` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ ≫ pullback.fst R.hom Q.hom ≫ R.hom = _`. Rewrite using `[pullback.lift_fst_assoc, Over.w v]), ?_⟩`. Use `Fin.cases ?_ (fun i => ?_)` and prove the remaining obligations. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [a, Fin.cons_zero, Over.comp_left, Over.homMk_left]`.

Conclude with `pullback.lift_snd _ _ _`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [b, Fin.cons_succ, Over.comp_left, Over.homMk_left, ← hv i]`. Rewrite using `[pullback.lift_fst_assoc]`. Take `⟨n, ⟨e⟩⟩` from `Finite.exists_equiv_fin J`.

Take `⟨R, p, ha, hf, hu⟩` from `key n`. Use `⟨R, fun j => p (e j), ha, hf, fun T u => ?_⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `hu T (fun i => u (e.symm i))`. Conclude with `⟨v, fun j => by simpa using hv (e j)⟩`.
-/
theorem exists_power {X : Scheme.{0}} (Q : Over X) [IsAffineHom Q.hom] [Flat Q.hom] (J : Type) [Finite J] :
    ∃ (R : Over X) (p : J → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧
      ∀ (T : Over X) (u : J → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i := by

  have key : ∀ n : ℕ, ∃ (R : Over X) (p : Fin n → (R ⟶ Q)), IsAffineHom R.hom ∧ Flat R.hom ∧
      ∀ (T : Over X) (u : Fin n → (T ⟶ Q)), ∃ v : T ⟶ R, ∀ i, v ≫ p i = u i := by
    intro n
    induction n with
    | zero =>
      refine ⟨Over.mk (𝟙 X), fun i => i.elim0, ?_, ?_, fun T u => ⟨Over.homMk T.hom (by simp), fun i => i.elim0⟩⟩
      · show IsAffineHom (𝟙 X)
        infer_instance
      · show Flat (𝟙 X)
        infer_instance
    | succ n ih =>
      obtain ⟨R, p, hRa, hRf, hR⟩ := ih
      have ha : IsAffineHom (pullback.fst R.hom Q.hom) :=
        MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
          (IsPullback.of_hasPullback R.hom Q.hom).flip ‹_›
      let R' : Over X := Over.mk (pullback.fst R.hom Q.hom ≫ R.hom)
      let a : R' ⟶ Q := Over.homMk (pullback.snd R.hom Q.hom) pullback.condition.symm
      let b : R' ⟶ R := Over.homMk (pullback.fst R.hom Q.hom) rfl
      refine ⟨R', Fin.cons (α := fun _ => R' ⟶ Q) a (fun i => b ≫ p i), ?_, ?_, ?_⟩
      · show IsAffineHom (pullback.fst R.hom Q.hom ≫ R.hom)
        infer_instance
      · show Flat (pullback.fst R.hom Q.hom ≫ R.hom)
        infer_instance
      · intro T u
        obtain ⟨v, hv⟩ := hR T (fun i => u i.succ)
        have hc : v.left ≫ R.hom = (u 0).left ≫ Q.hom := by rw [Over.w v, Over.w (u 0)]
        refine ⟨Over.homMk (pullback.lift v.left (u 0).left hc) (by
          change _ ≫ pullback.fst R.hom Q.hom ≫ R.hom = _
          rw [pullback.lift_fst_assoc, Over.w v]), ?_⟩
        refine Fin.cases ?_ (fun i => ?_)
        · apply Over.OverMorphism.ext
          simp only [a, Fin.cons_zero, Over.comp_left, Over.homMk_left]
          exact pullback.lift_snd _ _ _
        · apply Over.OverMorphism.ext
          simp only [b, Fin.cons_succ, Over.comp_left, Over.homMk_left, ← hv i]
          rw [pullback.lift_fst_assoc]
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin J
  obtain ⟨R, p, ha, hf, hu⟩ := key n
  refine ⟨R, fun j => p (e j), ha, hf, fun T u => ?_⟩
  obtain ⟨v, hv⟩ := hu T (fun i => u (e.symm i))
  exact ⟨v, fun j => by simpa using hv (e j)⟩

/- English proof (translation)
Establish `: IsAffine (pullback x0 R.hom)` using `inferInstance`. Set `e` to `(pullback x0 R.hom).isoSpec`. Take `⟨φ, hφ⟩ : ∃ φ : S →+* Γ(pullback x0 R.hom, ⊤), spMap φ = e.inv ≫ pullback.fst x0 R.hom` from `⟨_, Spec.map_preimage _⟩`. Establish `hw : (e.inv ≫ pullback.snd x0 R.hom) ≫ R.hom = (Over.mk (spMap φ ≫ x0)).hom`. Simplify using `[hφ, pullback.condition]`.

Use `⟨Γ(pullback x0 R.hom, ⊤), inferInstance, φ, Over.homMk (e.inv ≫ pullback.snd x0 R.hom) hw, ?_, ?_⟩` and prove the remaining obligations. Establish `hfl : Flat (spMap φ)`. Rewrite using `[hφ]`. Use `infer_instance`. Conclude with `(HasRingHomProperty.Spec_iff (P := @Flat)).mp hfl`.

Introduce `T _ ψ u`. Set `g : Sp T ⟶ pullback x0 R.hom` to `pullback.lift (spMap ψ) u.left (Over.w u).symm`. Take `⟨χ, hχ⟩ : ∃ χ : Γ(pullback x0 R.hom, ⊤) →+* T, spMap χ = g ≫ e.hom` from `⟨_, Spec.map_preimage _⟩`. Use `⟨χ, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : spMap (χ.comp φ) = spMap ψ`.

Express the relevant statement in the definitionally equal form `Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom χ) = _`. Rewrite using `[Spec.map_comp]`. Express the relevant statement in the definitionally equal form `spMap χ ≫ spMap φ = _`. Rewrite using `[hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc]`. Conclude with `pullback.lift_fst _ _ _`.

Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`. Rewrite using `[hχ]`. Express the relevant statement in the definitionally equal form `u.left = (g ≫ e.hom) ≫ e.inv ≫ pullback.snd x0 R.hom`. Rewrite using `[Category.assoc, Iso.hom_inv_id_assoc]`. Conclude with `(pullback.lift_snd _ _ _).symm`.
-/
theorem exists_point {X : Scheme.{0}} (R : Over X) [IsAffineHom R.hom] [Flat R.hom] (S : Type) [CommRing S]
    (x0 : Sp S ⟶ X) :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : Over.mk (spMap φ ≫ x0) ⟶ R), φ.Flat ∧
      ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : Over.mk (spMap ψ ≫ x0) ⟶ R),
        ∃ χ : B →+* T, χ.comp φ = ψ ∧ u.left = spMap χ ≫ w.left := by

  have : IsAffine (pullback x0 R.hom) := inferInstance
  let e := (pullback x0 R.hom).isoSpec
  obtain ⟨φ, hφ⟩ : ∃ φ : S →+* Γ(pullback x0 R.hom, ⊤), spMap φ = e.inv ≫ pullback.fst x0 R.hom :=
    ⟨_, Spec.map_preimage _⟩
  have hw : (e.inv ≫ pullback.snd x0 R.hom) ≫ R.hom = (Over.mk (spMap φ ≫ x0)).hom := by
    simp [hφ, pullback.condition]
  refine ⟨Γ(pullback x0 R.hom, ⊤), inferInstance, φ, Over.homMk (e.inv ≫ pullback.snd x0 R.hom) hw, ?_, ?_⟩
  · have hfl : Flat (spMap φ) := by
      rw [hφ]
      infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).mp hfl
  · intro T _ ψ u
    let g : Sp T ⟶ pullback x0 R.hom := pullback.lift (spMap ψ) u.left (Over.w u).symm
    obtain ⟨χ, hχ⟩ : ∃ χ : Γ(pullback x0 R.hom, ⊤) →+* T, spMap χ = g ≫ e.hom := ⟨_, Spec.map_preimage _⟩
    refine ⟨χ, ?_, ?_⟩
    · have h1 : spMap (χ.comp φ) = spMap ψ := by
        change Spec.map (CommRingCat.ofHom φ ≫ CommRingCat.ofHom χ) = _
        rw [Spec.map_comp]
        change spMap χ ≫ spMap φ = _
        rw [hχ, hφ, Category.assoc, Iso.hom_inv_id_assoc]
        exact pullback.lift_fst _ _ _
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    · rw [hχ]
      change u.left = (g ≫ e.hom) ≫ e.inv ≫ pullback.snd x0 R.hom
      rw [Category.assoc, Iso.hom_inv_id_assoc]
      exact (pullback.lift_snd _ _ _).symm

/- English proof (translation)
Establish `hm : ∀ {T : Over X} (u : T ⟶ A), u ^ k = u ≫ mulA A k`. Introduce `T u`. Rewrite using `[show mulA A k = 𝟙 A ^ k from rfl, MonObj.comp_pow, Category.comp_id]`. Set `Q : Over X` to `Over.mk (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left : _ ⟶ X)`. Establish `hjw : pullback.fst (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left ≫ A.hom = Q.hom`.

Rewrite using `[← Over.w (mulA A k), pullback.condition_assoc, Over.w]`. Conclude with `Category.comp_id _`. Set `j : Q ⟶ A` to `Over.homMk (pullback.fst _ _) hjw`. Use `⟨Q, j, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show IsAffineHom (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left) infer_instance`.

Use `show Flat (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left) infer_instance`. Rewrite using `[hm j]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `show (j ≫ mulA A k).left = (toUnit Q ≫ MonObj.one).left`. Rewrite using `[Over.comp_left, Over.comp_left]`.

Conclude with `pullback.condition`. Introduce `T u hu`. Establish `h0 : u ≫ mulA A k = toUnit T ≫ MonObj.one`. Rewrite using `[← hm u, hu]`. Both sides reduce to the same expression.

Establish `h1 : u.left ≫ (mulA A k).left = T.hom ≫ (MonObj.one : 𝟙_ (Over X) ⟶ A).left`. Establish `h2` using `congrArg (fun f => f.left) h0`. Simplify using `only [Over.comp_left] at h2`. Conclude with `h2`. Use `⟨Over.homMk (pullback.lift u.left T.hom h1) (pullback.lift_snd _ _ _), ?_⟩` and prove the remaining obligations.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left]`. Conclude with `pullback.lift_fst _ _ _`.
-/
theorem exists_kernel {X : Scheme.{0}} (A : Over X) [GrpObj A] (k : ℕ) [IsFinite (mulA A k).left]
    [Flat (mulA A k).left] :
    ∃ (Q : Over X) (j : Q ⟶ A), IsAffineHom Q.hom ∧ Flat Q.hom ∧ j ^ k = 1 ∧
      ∀ (T : Over X) (u : T ⟶ A), u ^ k = 1 → ∃ v : T ⟶ Q, v ≫ j = u := by

  have hm : ∀ {T : Over X} (u : T ⟶ A), u ^ k = u ≫ mulA A k := by
    intro T u
    rw [show mulA A k = 𝟙 A ^ k from rfl, MonObj.comp_pow, Category.comp_id]

  let Q : Over X := Over.mk (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left : _ ⟶ X)
  have hjw : pullback.fst (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left ≫ A.hom = Q.hom := by
    rw [← Over.w (mulA A k), pullback.condition_assoc, Over.w]
    exact Category.comp_id _
  let j : Q ⟶ A := Over.homMk (pullback.fst _ _) hjw
  refine ⟨Q, j, ?_, ?_, ?_, ?_⟩
  · show IsAffineHom (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left)
    infer_instance
  · show Flat (pullback.snd (mulA A k).left (MonObj.one : 𝟙_ (Over X) ⟶ A).left)
    infer_instance
  · rw [hm j]
    apply Over.OverMorphism.ext
    show (j ≫ mulA A k).left = (toUnit Q ≫ MonObj.one).left
    rw [Over.comp_left, Over.comp_left]
    exact pullback.condition
  · intro T u hu
    have h0 : u ≫ mulA A k = toUnit T ≫ MonObj.one := by
      rw [← hm u, hu]
      rfl
    have h1 : u.left ≫ (mulA A k).left = T.hom ≫ (MonObj.one : 𝟙_ (Over X) ⟶ A).left := by
      have h2 := congrArg (fun f => f.left) h0
      simp only [Over.comp_left] at h2
      exact h2
    refine ⟨Over.homMk (pullback.lift u.left T.hom h1) (pullback.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact pullback.lift_fst _ _ _

/- English proof (translation)
Take `⟨Q, j, hQa, hQf, hj, hQ⟩` from `exists_kernel A k`. Use `hQa` as an intermediate fact. Use `hQf` as an intermediate fact. Take `⟨R, p, hRa, hRf, hR⟩` from `exists_power Q J`. Use `hRa` as an intermediate fact.

Use `hRf` as an intermediate fact. Take `⟨B, iB, φ, w, hφ, hw⟩` from `exists_point R S x0`. Use `⟨B, iB, φ, fun i => w ≫ p i ≫ j, hφ, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `show (w ≫ p i ≫ j) ^ k = 1`. Rewrite using `[← Category.assoc, ← MonObj.comp_pow, hj, MonObj.comp_one]`.

Introduce `T _ ψ u hu choose v hv using fun i => hQ _ (u i) (hu i)`. Take `⟨v', hv'⟩` from `hR _ v`. Take `⟨χ, hχ, hχw⟩` from `hw T ψ v'`. Use `⟨χ, hχ, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← hv i, ← hv' i]`.

Simplify using `[hχw]`.
-/
theorem exists_tuple {X : Scheme.{0}} (A : Over X) [GrpObj A] (k : ℕ) [IsFinite (mulA A k).left]
    [Flat (mulA A k).left] (S : Type) [CommRing S] (x0 : Sp S ⟶ X) (J : Type) [Finite J] :
    ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (Over.mk (spMap φ ≫ x0) ⟶ A)), φ.Flat ∧
      (∀ i, w i ^ k = 1) ∧ ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : J → (Over.mk (spMap ψ ≫ x0) ⟶ A)),
        (∀ i, u i ^ k = 1) → ∃ χ : B →+* T, χ.comp φ = ψ ∧ ∀ i, (u i).left = spMap χ ≫ (w i).left := by
  obtain ⟨Q, j, hQa, hQf, hj, hQ⟩ := exists_kernel A k
  have := hQa
  have := hQf
  obtain ⟨R, p, hRa, hRf, hR⟩ := exists_power Q J
  have := hRa
  have := hRf
  obtain ⟨B, iB, φ, w, hφ, hw⟩ := exists_point R S x0
  refine ⟨B, iB, φ, fun i => w ≫ p i ≫ j, hφ, fun i => ?_, ?_⟩
  · show (w ≫ p i ≫ j) ^ k = 1
    rw [← Category.assoc, ← MonObj.comp_pow, hj, MonObj.comp_one]
  · intro T _ ψ u hu
    choose v hv using fun i => hQ _ (u i) (hu i)
    obtain ⟨v', hv'⟩ := hR _ v
    obtain ⟨χ, hχ, hχw⟩ := hw T ψ v'
    refine ⟨χ, hχ, fun i => ?_⟩
    rw [← hv i, ← hv' i]
    simp [hχw]

end TorsTuple

/- English proof (translation)
Introduce `hL E _ _ _ H Dw l Xo S _ x0 k hk J _`. Establish `hN` using `hL.mulN`. Unfold `MulNSt at hN`. Take `⟨hloc, -⟩` from `moduli_univ_polAV E H Dw l Xo`. Take `⟨hfin, hfl, -⟩` from `hN Xo.X (UnivPol.pol Xo) k hk`.

Establish `hfin' : IsFinite (mulA Xo.univ.t.G k).left` using `hfin`. Establish `hfl' : Flat (mulA Xo.univ.t.G k).left` using `hfl`. Conclude with `TorsTuple.exists_tuple Xo.univ.t.G k S x0 J`.
-/
theorem exists_flat_universal_torsion_tuple :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x0 : Sp S ⟶ Xo.X) (k : ℕ), 0 < k → ∀ (J : Type) [Fintype J], ∃ (B : Type) (_ : CommRing B) (φ : S →+* B) (w : J → (ptO Xo (spMap φ ≫ x0) ⟶ Xo.univ.t.G)), φ.Flat ∧ (∀ i, w i ^ k = 1) ∧ ∀ (T : Type) [CommRing T] (ψ : S →+* T) (u : J → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)), (∀ i, u i ^ k = 1) → ∃ χ : B →+* T, χ.comp φ = ψ ∧ ∀ i, (u i).left = spMap χ ≫ (w i).left := by
  intro hL E _ _ _ H Dw l Xo S _ x0 k hk J _

  have hN := hL.mulN
  unfold MulNSt at hN
  obtain ⟨hloc, -⟩ := moduli_univ_polAV E H Dw l Xo
  obtain ⟨hfin, hfl, -⟩ := hN Xo.X (UnivPol.pol Xo) k hk
  have hfin' : IsFinite (mulA Xo.univ.t.G k).left := hfin
  have hfl' : Flat (mulA Xo.univ.t.G k).left := hfl
  exact TorsTuple.exists_tuple Xo.univ.t.G k S x0 J

end GlobalTheory
