import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.TrivLocus

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, h⟩ σ`. Use `Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `congrFun h (σ i)`.

Introduce `h`. Assume the negation of the conclusion as `hn`. Establish `hinj : Function.Injective D.mulVec`. Introduce `v w e`. Assume the negation of the conclusion as `hvw`.

Conclude with `hn ⟨v - w, sub_ne_zero.2 hvw, by rw [Matrix.mulVec_sub, e, sub_self]⟩`. Establish `hcol : LinearIndependent K D.col` using `Matrix.mulVec_injective_iff.1 hinj`. Establish `hrank : D.rank = a`. Rewrite using `[← Matrix.rank_transpose]`. Use `LinearIndependent.rank_matrix (M := D.transpose) hcol` as an intermediate fact.

Simplify using `using this`. Take `⟨κ, e, -, hspan, hli⟩` from `exists_linearIndependent' K D.row`. Establish `: Finite κ` using `hli.finite`. Set `_ : Fintype κ` to `Fintype.ofFinite κ`. Establish `hcard : Fintype.card κ = a`.

Rewrite using `[← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row, hrank]`. Set `ε : Fin a ≃ κ` to `(Fintype.equivFinOfCardEq hcard).symm`. Establish `hli' : LinearIndependent K (D.submatrix (e ∘ ε) id).row` using `hli.comp ε ε.injective`. Establish `hu` using `(Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hli')`. Conclude with `hu.ne_zero (h _)`.
-/
theorem exists_ker_iff_minors {K : Type} [Field K] {a b : ℕ} (D : Matrix (Fin b) (Fin a) K) :
    (∃ v : Fin a → K, v ≠ 0 ∧ D.mulVec v = 0) ↔ ∀ σ : Fin a → Fin b, (D.submatrix σ id).det = 0 := by
  classical
  constructor
  · rintro ⟨v, hv, h⟩ σ
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv, ?_⟩
    funext i
    exact congrFun h (σ i)
  · intro h
    by_contra hn
    have hinj : Function.Injective D.mulVec := by
      intro v w e
      by_contra hvw
      exact hn ⟨v - w, sub_ne_zero.2 hvw, by rw [Matrix.mulVec_sub, e, sub_self]⟩
    have hcol : LinearIndependent K D.col := Matrix.mulVec_injective_iff.1 hinj
    have hrank : D.rank = a := by
      rw [← Matrix.rank_transpose]
      have := LinearIndependent.rank_matrix (M := D.transpose) hcol
      simpa using this
    obtain ⟨κ, e, -, hspan, hli⟩ := exists_linearIndependent' K D.row
    have : Finite κ := hli.finite
    let _ : Fintype κ := Fintype.ofFinite κ
    have hcard : Fintype.card κ = a := by
      rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row, hrank]
    let ε : Fin a ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
    have hli' : LinearIndependent K (D.submatrix (e ∘ ε) id).row := hli.comp ε ε.injective
    have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hli')
    exact hu.ne_zero (h _)

/- English proof (translation)
Establish `h` using `exists_ker_iff_minors (D.map g)`. Establish `h' : ∀ σ : Fin a → Fin b, ((D.map g).submatrix σ id).det = g (D.submatrix σ id).det` using `fun σ => by`. Rewrite using `[RingHom.map_det]`. Both sides reduce to the same expression. Simplify using `only [h'] at h`.

Simplify using `only [RingHom.mem_ker]`. Rewrite using `[← h, nontrivial_iff_exists_ne ⟨0, Matrix.mulVec_zero _⟩]`. Conclude with `⟨fun ⟨v, hv⟩ => ⟨v.1, fun e => hv (Subtype.ext e), v.2⟩, fun ⟨v, hv, e⟩ => ⟨⟨v, e⟩, fun e' => hv (congrArg Subtype.val e')⟩⟩`.
-/
theorem nontrivial_ker_iff {R K : Type} [CommRing R] [Field K] (g : R →+* K) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) :
    Nontrivial {v : Fin a → K // (D.map g).mulVec v = 0} ↔
      ∀ σ : Fin a → Fin b, (D.submatrix σ id).det ∈ RingHom.ker g := by
  have h := exists_ker_iff_minors (D.map g)
  have h' : ∀ σ : Fin a → Fin b, ((D.map g).submatrix σ id).det = g (D.submatrix σ id).det := fun σ => by
    rw [RingHom.map_det]; rfl
  simp only [h'] at h
  simp only [RingHom.mem_ker]
  rw [← h, nontrivial_iff_exists_ne ⟨0, Matrix.mulVec_zero _⟩]
  exact ⟨fun ⟨v, hv⟩ => ⟨v.1, fun e => hv (Subtype.ext e), v.2⟩,
    fun ⟨v, hv, e⟩ => ⟨⟨v, e⟩, fun e' => hv (congrArg Subtype.val e')⟩⟩

variable {X Y : Scheme.{0}}

def zeroSec (N : LB X) : LB.Sec N where
  f := fun _ => 0
  compat := fun _ _ => by rw [map_zero, map_zero, mul_zero]

/- English proof (translation)
Rewrite using `[nontrivial_iff_exists_ne (zeroSec N)]`. Use `exists_congr fun s => ?_` and prove the remaining obligations. Take `⟨sf, hs⟩` from `s`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Establish `: sf = fun _ => 0` using `funext hn`. Substitute `this` using the available equality. Conclude with `h rfl`.

Introduce and unpack `⟨i, hi⟩ h`. Conclude with `hi (congrArg (fun s => s.f i) h)`.
-/
theorem nontrivial_sec_iff (N : LB X) : Nontrivial (LB.Sec N) ↔ ∃ (s : LB.Sec N) (i : N.ι), s.f i ≠ 0 := by
  rw [nontrivial_iff_exists_ne (zeroSec N)]
  refine exists_congr fun s => ?_
  obtain ⟨sf, hs⟩ := s
  constructor
  · intro h
    by_contra hn
    push_neg at hn
    have : sf = fun _ => 0 := funext hn
    subst this
    exact h rfl
  · rintro ⟨i, hi⟩ h
    exact hi (congrArg (fun s => s.f i) h)

/- English proof (translation)
Use `congrArg (LB.mk (M.pull π).ι (M.pull π).U) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `j j'`. Express the relevant statement in the definitionally equal form `∏ _k : PUnit, _ = (∏ _k : PUnit, _) ^ t`. Use `Eq.trans ?_ (Finset.prod_zpow (G := Γ(Y, LB.wchart M (fun _ : PUnit => π) j ⊓ LB.wchart M (fun _ : PUnit => π) j')ˣ) _ _ t)` and prove the remaining obligations. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations.

Use `(zpow_one _).trans (Eq.trans ?_ (congrArg (· ^ t) (zpow_one _)).symm)` and prove the remaining obligations. Conclude with `(congrArg (res _) (map_zpow (pullU π _) (M.g (j k) (j' k)) t)).trans (map_zpow (res _) _ t)`.
-/
theorem pull_pw (M : LB X) (π : Y ⟶ X) (t : ℤ) : (pw M t).pull π = pw (M.pull π) t := by
  refine congrArg (LB.mk (M.pull π).ι (M.pull π).U) ?_
  funext j j'
  change ∏ _k : PUnit, _ = (∏ _k : PUnit, _) ^ t
  refine Eq.trans ?_ (Finset.prod_zpow (G := Γ(Y, LB.wchart M (fun _ : PUnit => π) j ⊓ LB.wchart M (fun _ : PUnit => π) j')ˣ) _ _ t)
  refine Finset.prod_congr rfl fun k _ => ?_
  refine (zpow_one _).trans (Eq.trans ?_ (congrArg (· ^ t) (zpow_one _)).symm)
  exact (congrArg (res _) (map_zpow (pullU π _) (M.g (j k) (j' k)) t)).trans (map_zpow (res _) _ t)

/- English proof (translation)
Establish `: Nonempty V` using `hV.to_subtype`. Introduce `e`. Conclude with `hx (map_injective_of_isIntegral X (homOfLE h) (e.trans (map_zero _).symm))`.
-/
theorem rs_ne_zero [IsIntegral X] {U V : X.Opens} (h : V ≤ U) (hV : (V : Set X).Nonempty) {x : Γ(X, U)}
    (hx : x ≠ 0) : rs X h x ≠ 0 := by
  have : Nonempty V := hV.to_subtype
  intro e
  exact hx (map_injective_of_isIntegral X (homOfLE h) (e.trans (map_zero _).symm))

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `: U = ⊥` using `TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.1 h)`. Substitute `this` using the available equality. Conclude with `hx (Subsingleton.elim _ _)`.
-/
theorem nonempty_of_ne_zero {U : X.Opens} {x : Γ(X, U)} (hx : x ≠ 0) : (U : Set X).Nonempty := by
  by_contra h
  have : U = ⊥ := TopologicalSpace.Opens.ext (Set.not_nonempty_iff_eq_empty.1 h)
  subst this
  exact hx (Subsingleton.elim _ _)

/- English proof (translation)
Rewrite using `[nontrivial_sec_iff, nontrivial_sec_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht⟩`. Take `⟨x⟩ : Nonempty X` from `inferInstance`. Establish `hx : x ∈ ⨆ i, N.U i` using `by rw [hN]; trivial`.

Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hx`. Establish `: Nonempty (N.U i)` using `⟨⟨x, hi⟩⟩`. Use `⟨⟨⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩, i, (t.s i).ne_zero⟩, ⟨⟨fun i => ((t.s i)⁻¹).val, fun i j => ?_⟩, i, ((t.s i)⁻¹).ne_zero⟩⟩` and prove the remaining obligations. Establish `h` using `congrArg (·⁻¹) (ht i j)`. Simplify using `only [mul_inv, ← map_inv] at h`.

Rewrite `h` using `[← zpow_neg_one (N.g i j)]`. Conclude with `congrArg Units.val h`. Introduce and unpack `⟨⟨s, i, hi⟩, ⟨s'', j, hj⟩⟩`. Set `s' : ∀ k : N.ι, Γ(X, N.U k)` to `s''.f`. Express the relevant statement in the definitionally equal form `N.ι at j`.

Express the relevant statement in the definitionally equal form `s' j ≠ 0 at hj`. Establish `hc : ∀ k l, rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s.f k * s' k) = rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s.f l * s' l)`. Introduce `k l`. Establish `h₁ : rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s.f k) = (N.g k l).val * rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s.f l)` using `s.compat k l`. Establish `h₂ : rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s' k) = (N.g k l ^ (-1 : ℤ)).val * rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s' l)` using `s''.compat k l`.

Rewrite using `[map_mul, map_mul, h₁, h₂, _root_.mul_mul_mul_comm, ← Units.val_mul, zpow_neg_one, mul_inv_cancel, Units.val_one, _root_.one_mul]`. Take `⟨h, hh, -⟩` from `X.sheaf.existsUnique_gluing' N.U ⊤ (fun _ => homOfLE le_top) hN.ge (fun k => s.f k * s' k) hc`. Express the relevant statement in the definitionally equal form `Γ(X, ⊤) at h`. Establish `hh' : ∀ k, rs X (le_top : N.U k ≤ ⊤) h = s.f k * s' k` using `hh`. Establish `hne : (↑(N.U i ⊓ N.U j) : Set X).Nonempty` using `nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen (nonempty_of_ne_zero hi) (nonempty_of_ne_zero hj)`.

Establish `hsj : s.f j ≠ 0`. Introduce `e`. Establish `h₁ : rs X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (s.f i) = (N.g i j).val * rs X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (s.f j)` using `s.compat i j`. Rewrite `h₁` using `[e, map_zero, mul_zero]`. Conclude with `rs_ne_zero _ hne hi h₁`.

Establish `: Nonempty (N.U j)` using `(nonempty_of_ne_zero hsj).to_subtype`. Establish `h0 : h ≠ 0`. Introduce `e`. Use `hh' j` as an intermediate fact. Rewrite `this` using `[e, map_zero]`.

Conclude with `mul_ne_zero hsj hj this.symm`. Establish `hu : IsUnit h`. Take `⟨c, hc⟩` from `hX.mul_inv_cancel h0`. Conclude with `IsUnit.of_mul_eq_one c hc`. Establish `hs : ∀ k, IsUnit (s.f k)` using `fun k => isUnit_of_mul_isUnit_left (hh' k ▸ hu.map (rs X (le_top : N.U k ≤ ⊤)))`.

Conclude with `⟨⟨fun k => (hs k).unit⟩, fun k l => Units.ext (s.compat k l)⟩`.
-/
theorem triv_iff [IsIntegral X] (hX : IsField Γ(X, ⊤)) (N : LB X) (hN : ⨆ i, N.U i = ⊤) :
    Triv N ↔ Nontrivial (LB.Sec N) ∧ Nontrivial (LB.Sec (pw N (-1))) := by
  rw [nontrivial_sec_iff, nontrivial_sec_iff]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨x⟩ : Nonempty X := inferInstance
    have hx : x ∈ ⨆ i, N.U i := by rw [hN]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    have : Nonempty (N.U i) := ⟨⟨x, hi⟩⟩
    refine ⟨⟨⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩, i, (t.s i).ne_zero⟩,
      ⟨⟨fun i => ((t.s i)⁻¹).val, fun i j => ?_⟩, i, ((t.s i)⁻¹).ne_zero⟩⟩
    have h := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at h
    rw [← zpow_neg_one (N.g i j)] at h
    exact congrArg Units.val h
  · rintro ⟨⟨s, i, hi⟩, ⟨s'', j, hj⟩⟩
    let s' : ∀ k : N.ι, Γ(X, N.U k) := s''.f
    change N.ι at j
    change s' j ≠ 0 at hj
    have hc : ∀ k l, rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s.f k * s' k) =
        rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s.f l * s' l) := by
      intro k l
      have h₁ : rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s.f k) =
        (N.g k l).val * rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s.f l) := s.compat k l
      have h₂ : rs X (inf_le_left : N.U k ⊓ N.U l ≤ N.U k) (s' k) =
        (N.g k l ^ (-1 : ℤ)).val * rs X (inf_le_right : N.U k ⊓ N.U l ≤ N.U l) (s' l) := s''.compat k l
      rw [map_mul, map_mul, h₁, h₂, _root_.mul_mul_mul_comm, ← Units.val_mul, zpow_neg_one, mul_inv_cancel,
        Units.val_one, _root_.one_mul]
    obtain ⟨h, hh, -⟩ := X.sheaf.existsUnique_gluing' N.U ⊤ (fun _ => homOfLE le_top) hN.ge
      (fun k => s.f k * s' k) hc
    change Γ(X, ⊤) at h
    have hh' : ∀ k, rs X (le_top : N.U k ≤ ⊤) h = s.f k * s' k := hh
    have hne : (↑(N.U i ⊓ N.U j) : Set X).Nonempty :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen (nonempty_of_ne_zero hi) (nonempty_of_ne_zero hj)
    have hsj : s.f j ≠ 0 := by
      intro e
      have h₁ : rs X (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) (s.f i) =
        (N.g i j).val * rs X (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) (s.f j) := s.compat i j
      rw [e, map_zero, mul_zero] at h₁
      exact rs_ne_zero _ hne hi h₁
    have : Nonempty (N.U j) := (nonempty_of_ne_zero hsj).to_subtype
    have h0 : h ≠ 0 := by
      intro e
      have := hh' j
      rw [e, map_zero] at this
      exact mul_ne_zero hsj hj this.symm
    have hu : IsUnit h := by
      obtain ⟨c, hc⟩ := hX.mul_inv_cancel h0
      exact IsUnit.of_mul_eq_one c hc
    have hs : ∀ k, IsUnit (s.f k) := fun k =>
      isUnit_of_mul_isUnit_left (hh' k ▸ hu.map (rs X (le_top : N.U k ≤ ⊤)))
    exact ⟨⟨fun k => (hs k).unit⟩, fun k l => Units.ext (s.compat k l)⟩

/- English proof (translation)
Establish `: IsIntegral X'` using `GeometricallyIntegral.geometrically_isIntegral _ _ _ h`. Establish `: IsProper f'` using `MorphismProperty.of_isPullback (P := @IsProper) h inferInstance`. Take `⟨E, -⟩` from `P.sec K g X' π f' h`. Take `⟨E', -⟩` from `Q.sec K g X' π f' h`. Rewrite using `[triv_iff (isField_of_universallyClosed K f') _ (LB.isLB_linComb hM _ _).cover, ← pull_pw, ← nontrivial_ker_iff, ← nontrivial_ker_iff, E.nontrivial_congr, E'.nontrivial_congr]`.
-/
theorem triv_fibre_iff {R : Type} [CommRing R] {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (hM : M.IsLB)
    (P : Perf f M) (Q : Perf f (pw M (-1))) [IsProper f] [GeometricallyIntegral f]
    {K : Type} [Field K] (g : R →+* K) {X' : Scheme.{0}} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of K)}
    (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g))) :
    Triv (M.pull π) ↔ (∀ σ : Fin P.a → Fin P.b, (P.D₀.submatrix σ id).det ∈ RingHom.ker g) ∧
      ∀ σ : Fin Q.a → Fin Q.b, (Q.D₀.submatrix σ id).det ∈ RingHom.ker g := by
  have : IsIntegral X' := GeometricallyIntegral.geometrically_isIntegral _ _ _ h
  have : IsProper f' := MorphismProperty.of_isPullback (P := @IsProper) h inferInstance
  obtain ⟨E, -⟩ := P.sec K g X' π f' h
  obtain ⟨E', -⟩ := Q.sec K g X' π f' h
  rw [triv_iff (isField_of_universallyClosed K f') _ (LB.isLB_linComb hM _ _).cover, ← pull_pw,
    ← nontrivial_ker_iff, ← nontrivial_ker_iff, E.nontrivial_congr, E'.nontrivial_congr]

/- English proof (translation)
Introduce and unpack `R _ X f M hM ⟨P⟩ ⟨Q⟩ _ _`. Use `PrimeSpectrum.isClosed_zeroLocus ((Set.range fun σ : Fin P.a → Fin P.b => (P.D₀.submatrix σ id).det) ∪ Set.range fun σ : Fin Q.a → Fin Q.b => (Q.D₀.submatrix σ id).det)` and compare the differences between its conclusion and the goal. Use extensionality with `p`. Rewrite using `[PrimeSpectrum.mem_zeroLocus, Set.union_subset_iff, Set.range_subset_iff, Set.range_subset_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨K, _, g, X', π, f', hg, h, ht⟩`. Rewrite using `[← hg]`. Conclude with `(triv_fibre_iff hM P Q g h).1 ht`. Introduce `hp`. Establish `hk : RingHom.ker (algebraMap R p.asIdeal.ResidueField) = p.asIdeal` using `Ideal.ker_algebraMap_residueField _`.

Use `⟨p.asIdeal.ResidueField, inferInstance, algebraMap R _, _, _, _, hk, IsPullback.of_hasPullback _ _, ?_⟩` and prove the remaining obligations. Use `(triv_fibre_iff hM P Q _ (IsPullback.of_hasPullback _ _)).2 ?_` and prove the remaining obligations. Rewrite using `[hk]`. Conclude with `hp`.
-/
theorem isClosed_trivLocus :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Nonempty (Perf f M) → Nonempty (Perf f (pw M (-1))) → IsProper f → GeometricallyIntegral f → IsClosed {p : PrimeSpectrum R | ∃ (K : Type) (_ : Field K) (g : R →+* K) (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of K)), RingHom.ker g = p.asIdeal ∧ IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) ∧ Triv (M.pull π)} := by
  rintro R _ X f M hM ⟨P⟩ ⟨Q⟩ _ _
  convert PrimeSpectrum.isClosed_zeroLocus
    ((Set.range fun σ : Fin P.a → Fin P.b => (P.D₀.submatrix σ id).det) ∪
      Set.range fun σ : Fin Q.a → Fin Q.b => (Q.D₀.submatrix σ id).det)
  ext p
  rw [PrimeSpectrum.mem_zeroLocus, Set.union_subset_iff, Set.range_subset_iff, Set.range_subset_iff]
  constructor
  · rintro ⟨K, _, g, X', π, f', hg, h, ht⟩
    rw [← hg]
    exact (triv_fibre_iff hM P Q g h).1 ht
  · intro hp
    have hk : RingHom.ker (algebraMap R p.asIdeal.ResidueField) = p.asIdeal := Ideal.ker_algebraMap_residueField _
    refine ⟨p.asIdeal.ResidueField, inferInstance, algebraMap R _, _, _, _, hk, IsPullback.of_hasPullback _ _, ?_⟩
    refine (triv_fibre_iff hM P Q _ (IsPullback.of_hasPullback _ _)).2 ?_
    rw [hk]
    exact hp

end GlobalTheory.TrivLocus
