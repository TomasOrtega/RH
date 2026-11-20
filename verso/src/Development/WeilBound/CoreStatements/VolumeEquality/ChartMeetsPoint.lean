import Development.WeilBound.CoreStatements.VolumeEquality.ChartMeetsForm

noncomputable section

namespace SheetDecomposition.ChartForm

open AlgebraicGeometry CategoryTheory MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePoints

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Rewrite using `[Scheme.stalkClosedPointTo_comp]`. Use `erw [Scheme.Hom.germ_stalkMap_assoc hV.fromSpec V _ h]`. Rewrite using `[IsAffineOpen.fromSpec_app_self, Category.assoc, TopCat.Presheaf.germ_res_assoc]`. Use `erw [Scheme.germ_stalkClosedPointTo_Spec φ]`. Conclude with `Iso.inv_hom_id_assoc _ _`.
-/
theorem germ_point {V : X.Opens} (hV : IsAffineOpen V) {R : CommRingCat} [IsLocalRing R] (φ : Γ(X, V) ⟶ R)
    (h : (Spec.map φ ≫ hV.fromSpec) (IsLocalRing.closedPoint R) ∈ V) :
    X.presheaf.germ V _ h ≫ Scheme.stalkClosedPointTo (Spec.map φ ≫ hV.fromSpec) = φ := by
  rw [Scheme.stalkClosedPointTo_comp]
  erw [Scheme.Hom.germ_stalkMap_assoc hV.fromSpec V _ h]
  rw [IsAffineOpen.fromSpec_app_self, Category.assoc, TopCat.Presheaf.germ_res_assoc]
  erw [Scheme.germ_stalkClosedPointTo_Spec φ]
  exact Iso.inv_hom_id_assoc _ _

/- English proof (translation)
Take `⟨h, s₁, h₁, h₂⟩` from `ha`. Take `⟨h', s₂, h₃, h₄⟩` from `hb`. Use `⟨h, s₁ + s₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, h₁]`. Conclude with `congrArg (a + ·) h₃`.

Conclude with `((Scheme.stalkClosedPointTo z).hom.map_add s₁ s₂).trans (by rw [h₂, h₄])`.
-/
private theorem valAt_add_volume_equality {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    {a b : Ω} {r s : R} (ha : ValAt ξ z a r) (hb : ValAt ξ z b s) : ValAt ξ z (a + b) (r + s) := by
  obtain ⟨h, s₁, h₁, h₂⟩ := ha
  obtain ⟨h', s₂, h₃, h₄⟩ := hb
  refine ⟨h, s₁ + s₂, ?_, ?_⟩
  · rw [map_add, h₁]
    exact congrArg (a + ·) h₃
  · exact ((Scheme.stalkClosedPointTo z).hom.map_add s₁ s₂).trans (by rw [h₂, h₄])

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩`.
-/
private theorem valAt_intCast' {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (h : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨h, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

/- English proof (translation)
Establish `hx : (fun c' : (k : Unit) → (fun _ : Unit => κ) k => ∏ k, (fun p : (Σ _ : Unit, κ) => x p.2) ⟨k, c' k⟩) = fun c' : Unit → κ => x (c' ())`. Use function extensionality and compare the values at `c'`. Simplify using the standard rewrite rules. Establish `hin : ∀ (c' : Unit → κ) (p : Cpt ξ), InChart ξ (fun c' : Unit → κ => x (c' ())) c' p ↔ InChart ξ x (c' ()) p`. Introduce `c' p`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h1⟩`. Conclude with `⟨h0, fun j => h1 (fun _ => j)⟩`. Introduce and unpack `⟨h0, h1⟩`. Conclude with `⟨h0, fun c'' => h1 (c'' ())⟩`.

Establish `hr : ∀ c' : Unit → κ, (Set.range fun j' : Unit → κ => x (j' ()) / x (c' ())) = Set.range fun j => x j / x (c' ())`. Introduce `c'`. Use extensionality with `a`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨j', rfl⟩`.

Conclude with `⟨j' (), rfl⟩`. Introduce and unpack `⟨j, rfl⟩`. Conclude with `⟨fun _ => j, rfl⟩`. Rewrite using `[hx]`. Use `⟨T.gen, fun p => ?_, fun c' hc' => ?_, fun c' hc' a => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc⟩` from `T.cover p`. Conclude with `⟨fun _ => c, (hin _ p).2 hc⟩`. Take `⟨U, hU, hq⟩` from `T.affine (c' ()) hc'`. Conclude with `⟨U, hU, fun q => (hq q).trans (exists_congr fun h => (hin c' ⟨q, h⟩).symm)⟩`. Rewrite using `[hr c', T.ring (c' ()) hc' a]`.

Conclude with `forall_congr' fun p => imp_congr_left (hin c' p).symm`.
-/
private theorem coordTie_unit_prod {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) :
    CoordTie ℤ ξ (fun c' : (k : Unit) → (fun _ : Unit => κ) k =>
      ∏ k, (fun p : (Σ _ : Unit, κ) => x p.2) ⟨k, c' k⟩) := by
  have hx : (fun c' : (k : Unit) → (fun _ : Unit => κ) k =>
      ∏ k, (fun p : (Σ _ : Unit, κ) => x p.2) ⟨k, c' k⟩) = fun c' : Unit → κ => x (c' ()) := by
    funext c'
    simp
  have hin : ∀ (c' : Unit → κ) (p : Cpt ξ),
      InChart ξ (fun c' : Unit → κ => x (c' ())) c' p ↔ InChart ξ x (c' ()) p := by
    intro c' p
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h0, fun j => h1 (fun _ => j)⟩
    · rintro ⟨h0, h1⟩
      exact ⟨h0, fun c'' => h1 (c'' ())⟩
  have hr : ∀ c' : Unit → κ, (Set.range fun j' : Unit → κ => x (j' ()) / x (c' ())) =
      Set.range fun j => x j / x (c' ()) := by
    intro c'
    ext a
    constructor
    · rintro ⟨j', rfl⟩
      exact ⟨j' (), rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨fun _ => j, rfl⟩
  rw [hx]
  refine ⟨T.gen, fun p => ?_, fun c' hc' => ?_, fun c' hc' a => ?_⟩
  · obtain ⟨c, hc⟩ := T.cover p
    exact ⟨fun _ => c, (hin _ p).2 hc⟩
  · obtain ⟨U, hU, hq⟩ := T.affine (c' ()) hc'
    exact ⟨U, hU, fun q => (hq q).trans (exists_congr fun h => (hin c' ⟨q, h⟩).symm)⟩
  · rw [hr c', T.ring (c' ()) hc' a]
    exact forall_congr' fun p => imp_congr_left (hin c' p).symm

/- English proof (translation)
Establish `T'` using `coordTie_unit_prod T`. Establish `hgen : ∀ j, x j / x c ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)` using `fun j => Algebra.subset_adjoin ⟨j, rfl⟩`. Set `w : (Σ _ : Unit, κ) → ℂ` to `fun p => ψ ⟨x p.2 / x c, hgen p.2⟩`. Establish `hw1 : ∀ k : Unit, w ⟨k, c⟩ = 1`. Introduce `k`.

Establish `e : (⟨x c / x c, hgen c⟩ : Algebra.adjoin ℤ (Set.range fun j => x j / x c)) = 1` using `Subtype.ext (div_self hc)`. Simplify using `only [w, e, map_one]`. Establish `hu : ∀ k : Unit, ∃ c' : κ, IsUnit (w ⟨k, c'⟩)` using `fun k => ⟨c, by rw [hw1 k]; exact isUnit_one⟩`. Establish `hk : ∀ g ∈ mCoordIdeal (fun p : (Σ _ : Unit, κ) => x p.2), aeval w g = 0` using `TiePoints.aeval_eq_zero_of_ratio (fun p : (Σ _ : Unit, κ) => x p.2) (fun _ => c) (fun _ => hc) w (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).toSubring ψ (fun p => ⟨x p.2 / x c, hgen p.2⟩) (fun _ => rfl) (fun p => by rw [hw1, mul_one])`. Take `⟨z, hz, hzc⟩` from `(TiePoints.existsUnique_point T' w hu hk).exists`.

Establish `hval : ∀ i, ValAt ξ z (x i / x c) (ψ ⟨x i / x c, hgen i⟩)`. Introduce `i`. Take `⟨r, hr, hwr⟩` from `(hzc.2 () c (by rw [hw1]; exact isUnit_one)).2 i`. Rewrite `hwr` using `[hw1, mul_one]`. Establish `e : ψ ⟨x i / x c, hgen i⟩ = r` using `hwr`.

Rewrite using `[e]`. Conclude with `hr`. Use `⟨z, hz, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨a, ha⟩`. Proceed by induction on `ha using Algebra.adjoin_induction with`.

Consider the case `mem a ha`. Take `⟨i, rfl⟩` from `ha`. Conclude with `hval i`. Consider the case `algebraMap n`. Establish `e : (⟨algebraMap ℤ Ω n, Subalgebra.algebraMap_mem _ n⟩ : Algebra.adjoin ℤ (Set.range fun j => x j / x c)) = (n : Algebra.adjoin ℤ (Set.range fun j => x j / x c))` using `Subtype.ext (by simp)`.

Rewrite using `[e, map_intCast]`. Simplify using `using valAt_intCast' hz n`. Consider the case `add a b ha hb iha ihb => show ValAt ξ z (a + b) (ψ (⟨a, ha⟩ + ⟨b, hb⟩))`. Rewrite using `[map_add]`. Conclude with `valAt_add_volume_equality iha ihb`.

Consider the case `mul a b ha hb iha ihb => show ValAt ξ z (a * b) (ψ (⟨a, ha⟩ * ⟨b, hb⟩))`. Rewrite using `[map_mul]`. Conclude with `TiePoints.valAt_mul T.gen iha ihb`.
-/
theorem exists_point_hom {κ : Type} {x : κ → Ω} (T : CoordTie ℤ ξ x) (c : κ) (hc : x c ≠ 0)
    (ψ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* ℂ) :
    ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, genPt ξ ⤳ centre z ∧
      ∀ a : Algebra.adjoin ℤ (Set.range fun j => x j / x c), ValAt ξ z (a : Ω) (ψ a) := by
  have T' := coordTie_unit_prod T
  have hgen : ∀ j, x j / x c ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) :=
    fun j => Algebra.subset_adjoin ⟨j, rfl⟩
  let w : (Σ _ : Unit, κ) → ℂ := fun p => ψ ⟨x p.2 / x c, hgen p.2⟩
  have hw1 : ∀ k : Unit, w ⟨k, c⟩ = 1 := by
    intro k
    have e : (⟨x c / x c, hgen c⟩ : Algebra.adjoin ℤ (Set.range fun j => x j / x c)) = 1 :=
      Subtype.ext (div_self hc)
    simp only [w, e, map_one]
  have hu : ∀ k : Unit, ∃ c' : κ, IsUnit (w ⟨k, c'⟩) := fun k => ⟨c, by rw [hw1 k]; exact isUnit_one⟩
  have hk : ∀ g ∈ mCoordIdeal (fun p : (Σ _ : Unit, κ) => x p.2), aeval w g = 0 :=
    TiePoints.aeval_eq_zero_of_ratio (fun p : (Σ _ : Unit, κ) => x p.2) (fun _ => c) (fun _ => hc) w
      (Algebra.adjoin ℤ (Set.range fun j => x j / x c)).toSubring ψ
      (fun p => ⟨x p.2 / x c, hgen p.2⟩) (fun _ => rfl) (fun p => by rw [hw1, mul_one])
  obtain ⟨z, hz, hzc⟩ := (TiePoints.existsUnique_point T' w hu hk).exists
  have hval : ∀ i, ValAt ξ z (x i / x c) (ψ ⟨x i / x c, hgen i⟩) := by
    intro i
    obtain ⟨r, hr, hwr⟩ := (hzc.2 () c (by rw [hw1]; exact isUnit_one)).2 i
    rw [hw1, mul_one] at hwr
    have e : ψ ⟨x i / x c, hgen i⟩ = r := hwr
    rw [e]
    exact hr
  refine ⟨z, hz, ?_⟩
  rintro ⟨a, ha⟩
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    exact hval i
  | algebraMap n =>
    have e : (⟨algebraMap ℤ Ω n, Subalgebra.algebraMap_mem _ n⟩ :
        Algebra.adjoin ℤ (Set.range fun j => x j / x c)) = (n : Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
      Subtype.ext (by simp)
    rw [e, map_intCast]
    simpa using valAt_intCast' hz n
  | add a b ha hb iha ihb =>
    show ValAt ξ z (a + b) (ψ (⟨a, ha⟩ + ⟨b, hb⟩))
    rw [map_add]
    exact valAt_add_volume_equality iha ihb
  | mul a b ha hb iha ihb =>
    show ValAt ξ z (a * b) (ψ (⟨a, ha⟩ * ⟨b, hb⟩))
    rw [map_mul]
    exact TiePoints.valAt_mul T.gen iha ihb

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Conclude with `(TiePoints.existsUnique_point T w hu hk).exists`.
-/
theorem exists_point {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}
    (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (w : (Σ k, J k) → ℂ) (hu : ∀ k, ∃ c, IsUnit (w ⟨k, c⟩)) (hk : ∀ g ∈ mCoordIdeal y, aeval w g = 0) :
    ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w := by
  exact (TiePoints.existsUnique_point T w hu hk).exists

end SheetDecomposition.ChartForm
