import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeEqSpanOfIsFrameAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundOfFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValFam
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombMatrixMulStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombIdentityMatrixStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenvectorLinearCombinationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFieldExtensionStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemSpanOfIotaMultiProportionalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiChangeOfBasisDetStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiNeZeroOfLinIndepStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationTangentCombStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationFieldExtStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentPointCmEigenFrameStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Lemmas
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {F : Type} [Field F] {x : Sp F ⟶ S}

/- English proof (translation)
The claim follows from `GlobalTheory.T.is_comb_matrix_mul S G F x m n k v u w A C hv hC hA`.
-/
theorem comb_mul {m n k : ℕ} {v : Fin n → (epsAt x ⟶ G)} {u : Fin m → (epsAt x ⟶ G)} {w : Fin k → (epsAt x ⟶ G)}
    {A : Matrix (Fin k) (Fin m) F} {C : Matrix (Fin m) (Fin n) F}
    (hv : ∀ i, IsTanAt G x (v i)) (hC : ∀ i, IsComb (C i) v (u i)) (hA : ∀ i, IsComb (A i) u (w i)) :
    ∀ i, IsComb ((A * C) i) v (w i) :=
  GlobalTheory.T.is_comb_matrix_mul S G F x m n k v u w A C hv hC hA

/- English proof (translation)
The claim follows from `GlobalTheory.T.is_comb_identity_matrix S G F x n v hv`.
-/
theorem comb_self {n : ℕ} {v : Fin n → (epsAt x ⟶ G)} (hv : ∀ i, IsTanAt G x (v i)) :
    ∀ i, IsComb ((1 : Matrix (Fin n) (Fin n) F) i) v (v i) :=
  GlobalTheory.T.is_comb_identity_matrix S G F x n v hv

/- English proof (translation)
The claim follows from `GlobalTheory.T.eigenvector_linear_combination S G F x P act σ n v cf w hv h`.
-/
theorem comb_eig {P : Type} [CommRing P] (act : OAct P G) (σ : P →+* F) {n : ℕ} {v : Fin n → (epsAt x ⟶ G)}
    {cf : Fin n → F} {w : epsAt x ⟶ G} (hv : ∀ i, IsEigVec act x σ (v i)) (h : IsComb cf v w) :
    IsEigVec act x σ w :=
  GlobalTheory.T.eigenvector_linear_combination S G F x P act σ n v cf w hv h

/- English proof (translation)
The claim follows from `GlobalTheory.T.is_comb_field_extension S G F x F' f x' hx n v cf w v' w' hv hw h`.
-/
theorem comb_base {F' : Type} [Field F'] (f : F →+* F') {x' : Sp F' ⟶ S} (hx : spMap f ≫ x = x') {n : ℕ}
    {v : Fin n → (epsAt x ⟶ G)} {cf : Fin n → F} {w : epsAt x ⟶ G} {v' : Fin n → (epsAt x' ⟶ G)}
    {w' : epsAt x' ⟶ G} (hv : ∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left)
    (hw : w'.left = spMap (dualMap f) ≫ w.left) (h : IsComb cf v w) : IsComb (fun i => f (cf i)) v' w' :=
  GlobalTheory.T.is_comb_field_extension S G F x F' f x' hx n v cf w v' w' hv hw h

/- English proof (translation)
The claim follows from `GlobalTheory.T.eigen_frame_field_extension S G F x P act σ F' f x' hx n v v' hv h`.
-/
theorem eigFrame_base [Smooth G.hom] {P : Type} [CommRing P] (act : OAct P G) (σ : P →+* F) {F' : Type} [Field F']
    (f : F →+* F') {x' : Sp F' ⟶ S} (hx : spMap f ≫ x = x') {n : ℕ} {v : Fin n → (epsAt x ⟶ G)}
    {v' : Fin n → (epsAt x' ⟶ G)} (hv : ∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left)
    (h : IsEigFrame act x σ v) : IsEigFrame act x' (f.comp σ) v' :=
  GlobalTheory.T.eigen_frame_field_extension S G F x P act σ F' f x' hx n v v' hv h

/- English proof (translation)
The claim follows from `GlobalTheory.T.mem_span_of_iota_multi_proportional Ω V n b e t he ht h i`.
-/
theorem wedge_span {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {n : ℕ} {b e : Fin n → V} {t : Ω}
    (he : LinearIndependent Ω e) (ht : t ≠ 0)
    (h : exteriorPower.ιMulti Ω n b = t • exteriorPower.ιMulti Ω n e) (i : Fin n) :
    b i ∈ Submodule.span Ω (Set.range e) :=
  GlobalTheory.T.mem_span_of_iota_multi_proportional Ω V n b e t he ht h i

/- English proof (translation)
The claim follows from `GlobalTheory.T.iota_multi_change_of_basis_det Ω V n e P`.
-/
theorem wedge_matrix {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {n : ℕ} (e : Fin n → V)
    (P : Matrix (Fin n) (Fin n) Ω) :
    exteriorPower.ιMulti Ω n (fun i => ∑ j, P i j • e j) = P.det • exteriorPower.ιMulti Ω n e :=
  GlobalTheory.T.iota_multi_change_of_basis_det Ω V n e P

/- English proof (translation)
The claim follows from `GlobalTheory.T.iota_multi_ne_zero_of_lin_indep Ω V n e he`.
-/
theorem wedge_ne_zero {Ω V : Type} [Field Ω] [AddCommGroup V] [Module Ω V] {n : ℕ} {e : Fin n → V}
    (he : LinearIndependent Ω e) : exteriorPower.ιMulti Ω n e ≠ 0 :=
  GlobalTheory.T.iota_multi_ne_zero_of_lin_indep Ω V n e he

end Lemmas

section Val2
variable {Y : Model Xo c β} {U : Set (Xo.XF c)}

/- English proof (translation)
The claim follows from `GlobalTheory.T.component_specialization_tangent_comb E H D l Xo c O β Y U Z F y n b v s r w hg h hs hw`.
-/
theorem valFam_comb (Z : CptOver Y U) {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c} {n : ℕ} {b : Fin n → Z.V}
    {v : Vecs y n} {s : Fin n → Z.Ω} {r : Fin n → F} {w : epsAt (under y) ⟶ Xo.univ.t.G}
    (hg : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (h : IsValFam Z y b v) (hs : ∀ j, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (s j) (r j)) (hw : IsComb r v w) :
    ∃ w', Z.M.ValAt (y ≫ Y.j) (∑ j, s j • b j) w' ∧ SameVec Y y w w' :=
  GlobalTheory.T.component_specialization_tangent_comb E H D l Xo c O β Y U Z F y n b v s r w hg h hs hw

/- English proof (translation)
The claim follows from `GlobalTheory.T.isValFam_of_field_extension E H D l Xo c O β Y U Z F F' f y y' hy n b v v' hv h`.
-/
theorem valFam_base (Z : CptOver Y U) {F F' : Type} [Field F] [Field F'] (f : F →+* F') {y : Sp F ⟶ Xo.XF c}
    {y' : Sp F' ⟶ Xo.XF c} (hy : y' = spMap f ≫ y) {n : ℕ} {b : Fin n → Z.V} {v : Vecs y n} {v' : Vecs y' n}
    (hv : ∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) (h : IsValFam Z y b v) : IsValFam Z y' b v' :=
  GlobalTheory.T.isValFam_of_field_extension E H D l Xo c O β Y U Z F F' f y y' hy n b v v' hv h

/- English proof (translation)
The claim follows from `GlobalTheory.T.component_point_cm_eigen_frame E H D l Xo c O β Y U Z τ hβ hτ F βF y hy hU h σ n b hb`.
-/
theorem exists_valFam (Z : CptOver Y U) (τ : E →+* ℂ)
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (hτ : τ (H.rt : E) = H.rt0) {F : Type} [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c)
    (hy : y ≫ pullback.snd _ _ = spMap βF) (hU : Set.range y ⊆ U) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (σ : E →+* ℂ) {n : ℕ} (b : Fin n → Z.V) (hb : (Z.eig σ).IsFrameAt b ⟨_, h⟩) :
    ∃ v : Vecs y n, IsValFam Z y b v ∧ IsEigFrame Xo.univ.t.act (under y) (βF.comp (tauIn c σ)) v :=
  GlobalTheory.T.component_point_cm_eigen_frame E H D l Xo c O β Y U Z τ hβ hτ F βF y hy hU h σ n b hb

end Val2

section Val
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {F : Type} [Field F] {z : Sp F ⟶ X}

/- English proof (translation)
Take `⟨hs, s, e1, e2⟩` from `h`. Take `⟨_, s', e1', e2'⟩` from `h'`. Establish `f2 : RootHt.Pick.valMap z s = r` using `e2`. Establish `f2' : RootHt.Pick.valMap z s' = r'` using `e2'`. Use `⟨hs, s * s', by rw [map_mul, e1, e1'], ?_⟩` and prove the remaining obligations.

Use `show RootHt.Pick.valMap z (s * s') = r * r'`. Rewrite using `[map_mul, f2, f2']`.
-/
theorem val_mul {a a' : Ω} {r r' : F} (h : ValAt ξ z a r) (h' : ValAt ξ z a' r') : ValAt ξ z (a * a') (r * r') := by
  obtain ⟨hs, s, e1, e2⟩ := h
  obtain ⟨_, s', e1', e2'⟩ := h'
  have f2 : RootHt.Pick.valMap z s = r := e2
  have f2' : RootHt.Pick.valMap z s' = r' := e2'
  refine ⟨hs, s * s', by rw [map_mul, e1, e1'], ?_⟩
  show RootHt.Pick.valMap z (s * s') = r * r'
  rw [map_mul, f2, f2']

/- English proof (translation)
Take `⟨hs, s, e1, e2⟩` from `h`. Establish `hu : IsUnit s` using `by haveI := RootHt.Pick.isLocalHom_valMap z`. Use `isUnit_of_map_unit (RootHt.Pick.valMap z) s ?_` and prove the remaining obligations. Establish `: RootHt.Pick.valMap z s = r` using `e2`. Rewrite using `[this]`.

Conclude with `hr.isUnit`. Take `⟨u, rfl⟩` from `hu`. Use `⟨hs, ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← e1]`. Conclude with `eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)`.

Establish `f2 : RootHt.Pick.valMap z (u : X.presheaf.stalk (centre z)) = r` using `e2 show RootHt.Pick.valMap z _ = r⁻¹`. Rewrite using `[← f2]`. Conclude with `eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)`.
-/
theorem val_inv {a : Ω} {r : F} (h : ValAt ξ z a r) (hr : r ≠ 0) : ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨hs, s, e1, e2⟩ := h
  have hu : IsUnit s := by
    haveI := RootHt.Pick.isLocalHom_valMap z
    refine isUnit_of_map_unit (RootHt.Pick.valMap z) s ?_
    have : RootHt.Pick.valMap z s = r := e2
    rw [this]
    exact hr.isUnit
  obtain ⟨u, rfl⟩ := hu
  refine ⟨hs, ((u⁻¹ : (X.presheaf.stalk (centre z))ˣ) : X.presheaf.stalk (centre z)), ?_, ?_⟩
  · rw [← e1]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)
  · have f2 : RootHt.Pick.valMap z (u : X.presheaf.stalk (centre z)) = r := e2
    show RootHt.Pick.valMap z _ = r⁻¹
    rw [← f2]
    exact eq_inv_of_mul_eq_one_left (by rw [← map_mul]; simp)

/- English proof (translation)
Establish `: ∀ i j, ∃ s : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ s = P i j ∧ (Scheme.stalkClosedPointTo z).hom s = A i j` using `fun i j => by`. Take `⟨_, s, e1, e2⟩` from `hP i j`. Conclude with `⟨s, e1, e2⟩`. Use `choose s e1 e2 using this`. Use `⟨h, (Matrix.of s).det, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `e1 i j`. Use `show RootHt.Pick.valMap z _ = A.det`.

Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `e2 i j`.
-/
theorem val_det (h : genPt ξ ⤳ centre z) {n : ℕ} {P : Matrix (Fin n) (Fin n) Ω} {A : Matrix (Fin n) (Fin n) F}
    (hP : ∀ i j, ValAt ξ z (P i j) (A i j)) : ValAt ξ z P.det A.det := by
  have : ∀ i j, ∃ s : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ s = P i j ∧
      (Scheme.stalkClosedPointTo z).hom s = A i j := fun i j => by
    obtain ⟨_, s, e1, e2⟩ := hP i j
    exact ⟨s, e1, e2⟩
  choose s e1 e2 using this
  refine ⟨h, (Matrix.of s).det, ?_, ?_⟩
  · rw [RingHom.map_det]
    congr 1
    ext i j
    exact e1 i j
  · show RootHt.Pick.valMap z _ = A.det
    rw [RingHom.map_det]
    congr 1
    ext i j
    exact e2 i j

end Val

/- English proof (translation)
Use `Spec.map_injective h` as an intermediate fact. Conclude with `congrArg CommRingCat.Hom.hom this`.
-/
theorem spMap_inj {R R' : Type} [CommRing R] [CommRing R'] {f g : R →+* R'} (h : spMap f = spMap g) : f = g := by
  have := Spec.map_injective h
  exact congrArg CommRingCat.Hom.hom this

section Gen
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {F : Type} [Field F] {x : Sp F ⟶ S}

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, fun i => LieTangent.epsScale x (cf i) ≫ v i, fun _ => rfl, rfl⟩`.
-/
theorem exists_comb {n : ℕ} (cf : Fin n → F) (v : Fin n → (epsAt x ⟶ G)) : ∃ w, IsComb cf v w :=
  ⟨_, fun i => LieTangent.epsScale x (cf i) ≫ v i, fun _ => rfl, rfl⟩

/- English proof (translation)
Establish `: ∀ i, ∃ cf, IsComb cf v' (v i)` using `fun i => (hv'.2 _ (hv.1 i)).exists`. Use `choose C hC using this`. Establish `ht : ∀ i, IsTanAt G x (v i)` using `fun i => (hv.1 i).1`. Establish `h1` using `comb_mul (C := A) (A := Matrix.of C) ht hA hC`. Establish `h2` using `comb_self (F := F) ht`.

Establish `h3 : Matrix.of C * A = 1`. Use extensionality with `i j`. Use `(hv.2 _ (hv.1 i)).unique (h1 i) (h2 i)` as an intermediate fact. Conclude with `congrFun this j`. Introduce `h0`.

Use `congrArg Matrix.det h3` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h0, mul_zero, Matrix.det_one]`. Conclude with `zero_ne_one this`.
-/
theorem frame_det {P : Type} [CommRing P] {act : OAct P G} {σ : P →+* F} {n : ℕ} {v v' : Fin n → (epsAt x ⟶ G)}
    {A : Matrix (Fin n) (Fin n) F} (hv : IsEigFrame act x σ v) (hv' : IsEigFrame act x σ v')
    (hA : ∀ i, IsComb (A i) v (v' i)) : A.det ≠ 0 := by
  have : ∀ i, ∃ cf, IsComb cf v' (v i) := fun i => (hv'.2 _ (hv.1 i)).exists
  choose C hC using this
  have ht : ∀ i, IsTanAt G x (v i) := fun i => (hv.1 i).1
  have h1 := comb_mul (C := A) (A := Matrix.of C) ht hA hC
  have h2 := comb_self (F := F) ht
  have h3 : Matrix.of C * A = 1 := by
    ext i j
    have := (hv.2 _ (hv.1 i)).unique (h1 i) (h2 i)
    exact congrFun this j
  intro h0
  have := congrArg Matrix.det h3
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

end Gen

section Main
variable {Y : Model Xo c β} {U : Set (Xo.XF c)}

/- English proof (translation)
Establish `h : genPt Z.ξ₀ ⤳ y (IsLocalRing.closedPoint F)` using `(Z.closure _).1 (hU ⟨_, rfl⟩)`. Conclude with `h.map Y.j.continuous`.
-/
theorem spec_pt (Z : CptOver Y U) {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c} (hU : Set.range y ⊆ U) :
    genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) := by
  have h : genPt Z.ξ₀ ⤳ y (IsLocalRing.closedPoint F) := (Z.closure _).1 (hU ⟨_, rfl⟩)
  exact h.map Y.j.continuous

/- English proof (translation)
Conclude with `⟨Y.jQ (y (IsLocalRing.closedPoint F)), rfl⟩`.
-/
theorem pt_mem_genFib (Z : CptOver Y U) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) : (⟨_, h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib := by
  exact ⟨Y.jQ (y (IsLocalRing.closedPoint F)), rfl⟩

/- English proof (translation)
Establish `hs` using `wedge_span hc.1 ht hw`. Establish `hce : ∀ j, c₀ j ∈ Z.eig σ ⟨_, h⟩` using `fun j => by`. Rewrite using `[hc.2]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`. Establish `hle : Submodule.span Z.Ω (Set.range c₀) ≤ eigSp Z.ρ (Z.inc.comp (tauIn c σ))`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `(hce j).2`. Establish `hb : ∀ i, b₁ i ∈ Z.eig σ ⟨_, h⟩` using `fun i => by`. Take `⟨v', hv', -⟩` from `h₁ i`.

Conclude with `⟨RootHt.Pick.mem_lat_of_val Z.M hv' h, hle (hs i)⟩`. Establish `hco : ∀ i, ∃ P : Fin n → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h⟩, ∑ j, P j • c₀ j = b₁ i` using `fun i => by`. Use `hb i` as an intermediate fact. Rewrite `this` using `[hc.2]`. Conclude with `(Submodule.mem_span_range_iff_exists_fun _).1 this`.

Use `choose P hP using hco`. Establish `hval : ∀ i j, ∃ r : F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (P i j : Z.Ω) r` using `fun i j => RootHt.Pick.exists_valAt (P i j).2`. Use `choose A hA using hval`. Set `Pm : Matrix (Fin n) (Fin n) Z.Ω` to `fun i j => (P i j : Z.Ω)`. Establish `hb' : b₁ = fun i => ∑ j, Pm i j • c₀ j`.

Use function extensionality and compare the values at `i`. Rewrite using `[← hP i]`. Both sides reduce to the same expression. Establish `hdet : t = Pm.det`. Establish `h1` using `wedge_matrix c₀ Pm`.

Rewrite `h1` using `[← hb', hw]`. Establish `h2 : (t - Pm.det) • exteriorPower.ιMulti Z.Ω n c₀ = 0`. Rewrite using `[sub_smul, h1, sub_self]`. Conclude with `sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right (wedge_ne_zero hc.1))`. Establish `hcomb : ∀ i, IsComb (Matrix.of A i) v₀ (v i)` using `fun i => by`.

Take `⟨w, hw'⟩` from `exists_comb (Matrix.of A i) v₀`. Take `⟨w', hw₁, hw₂⟩` from `valFam_comb Z (s := Pm i) h h₀ (hA i) hw'`. Take `⟨v', hv₁, hv₂⟩` from `h₁ i`. Establish `e : ∑ j, Pm i j • c₀ j = b₁ i` using `by rw [hb']`. Rewrite `hw₁` using `[e]`.

Establish `e'` using `LieModel.ValAt.unique Z.gen hw₁ hv₁`. Substitute `e'` using the available equality. Rewrite using `[← SameVec.unique_left hw₂ hv₂]`. Conclude with `hw'`. Use `⟨Matrix.of A, hcomb, frame_det hf₀ hf hcomb, ?_⟩` and prove the remaining obligations.

Rewrite using `[hdet]`. Conclude with `val_det h hA`.
-/
theorem expand (Z : CptOver Y U) {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (σ : E →+* ℂ) (σ' : 𝓞 E →+* F) {n : ℕ} {c₀ b₁ : Fin n → Z.V}
    {v₀ v : Vecs y n} {t : Z.Ω} (hc : (Z.eig σ).IsFrameAt c₀ ⟨_, h⟩) (h₀ : IsValFam Z y c₀ v₀)
    (h₁ : IsValFam Z y b₁ v) (hf₀ : IsEigFrame Xo.univ.t.act (under y) σ' v₀)
    (hf : IsEigFrame Xo.univ.t.act (under y) σ' v) (ht : t ≠ 0)
    (hw : exteriorPower.ιMulti Z.Ω n b₁ = t • exteriorPower.ιMulti Z.Ω n c₀) :
    ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, IsComb (A i) v₀ (v i)) ∧ A.det ≠ 0 ∧
      ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) t A.det := by
  have hs := wedge_span hc.1 ht hw
  have hce : ∀ j, c₀ j ∈ Z.eig σ ⟨_, h⟩ := fun j => by
    rw [hc.2]
    exact Submodule.subset_span ⟨j, rfl⟩
  have hle : Submodule.span Z.Ω (Set.range c₀) ≤ eigSp Z.ρ (Z.inc.comp (tauIn c σ)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact (hce j).2
  have hb : ∀ i, b₁ i ∈ Z.eig σ ⟨_, h⟩ := fun i => by
    obtain ⟨v', hv', -⟩ := h₁ i
    exact ⟨RootHt.Pick.mem_lat_of_val Z.M hv' h, hle (hs i)⟩
  have hco : ∀ i, ∃ P : Fin n → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h⟩, ∑ j, P j • c₀ j = b₁ i := fun i => by
    have := hb i
    rw [hc.2] at this
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose P hP using hco
  have hval : ∀ i j, ∃ r : F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (P i j : Z.Ω) r := fun i j =>
    RootHt.Pick.exists_valAt (P i j).2
  choose A hA using hval
  let Pm : Matrix (Fin n) (Fin n) Z.Ω := fun i j => (P i j : Z.Ω)
  have hb' : b₁ = fun i => ∑ j, Pm i j • c₀ j := by
    funext i
    rw [← hP i]
    rfl
  have hdet : t = Pm.det := by
    have h1 := wedge_matrix c₀ Pm
    rw [← hb', hw] at h1
    have h2 : (t - Pm.det) • exteriorPower.ιMulti Z.Ω n c₀ = 0 := by
      rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right (wedge_ne_zero hc.1))
  have hcomb : ∀ i, IsComb (Matrix.of A i) v₀ (v i) := fun i => by
    obtain ⟨w, hw'⟩ := exists_comb (Matrix.of A i) v₀
    obtain ⟨w', hw₁, hw₂⟩ := valFam_comb Z (s := Pm i) h h₀ (hA i) hw'
    obtain ⟨v', hv₁, hv₂⟩ := h₁ i
    have e : ∑ j, Pm i j • c₀ j = b₁ i := by rw [hb']
    rw [e] at hw₁
    have e' := LieModel.ValAt.unique Z.gen hw₁ hv₁
    subst e'
    rw [← SameVec.unique_left hw₂ hv₂]
    exact hw'
  refine ⟨Matrix.of A, hcomb, frame_det hf₀ hf hcomb, ?_⟩
  rw [hdet]
  exact val_det h hA

def IsRat (Z : CptOver Y U) (τ : E →+* ℂ) (a : ⋀[Z.Ω]^D.p Z.V)
    (b : ⋀[Z.Ω]^D.q Z.V) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (r : F) : Prop :=
  ∃ (βF : c.F →+* F) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (α κ : Z.Ω), IsFramed U τ βF y v w ∧
    a = α • exteriorPower.ιMulti Z.Ω D.p b₁ ∧ b = κ • exteriorPower.ιMulti Z.Ω D.q b₂ ∧
    IsValFam Z y b₁ v ∧ IsValFam Z y b₂ w ∧ ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (α / κ) r

def IsGen (Z : CptOver Y U) (τ : E →+* ℂ) (a : ⋀[Z.Ω]^D.p Z.V)
    (b : ⋀[Z.Ω]^D.q Z.V) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (r : F) : Prop :=
  ∃ (v₀ : Vecs y D.p) (w₀ : Vecs y D.q) (r₀ : F) (A : Matrix (Fin D.p) (Fin D.p) F)
    (B : Matrix (Fin D.q) (Fin D.q) F), IsRat Z τ a b y v₀ w₀ r₀ ∧ (∀ i, IsComb (A i) v₀ (v i)) ∧
    (∀ j, IsComb (B j) w₀ (w j)) ∧ A.det ≠ 0 ∧ r * A.det = r₀ * B.det

open Classical in

def repFn (Z : CptOver Y U) (τ : E →+* ℂ) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V) : FrameFn Xo c :=
  fun F _ y v w => if h : ∃ r, IsGen Z τ a b y v w r then h.choose else 0

variable (Z : CptOver Y U) (τ : E →+* ℂ) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V)

/- English proof (translation)
Establish `h` using `spec_pt Z hU`. Establish `hx` using `pt_mem_genFib Z y h`. Take `⟨hvb₁, hvb₂, -, -⟩` from `GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ`. Take `⟨W₁, hW₁, c₁, -, hc₁⟩` from `hvb₁ _ hx`. Take `⟨W₂, hW₂, c₂, -, hc₂⟩` from `hvb₂ _ hx`.

Establish `f₁` using `hc₁ _ hx hW₁`. Establish `f₂` using `hc₂ _ hx hW₂`. Take `⟨-, -, hco⟩` from `hg`. Take `⟨α', β', hα', -, hA, hB, e⟩` from `hco _ hx`. Rewrite `e` using `[_root_.one_mul]`.

Substitute `e` using the available equality. Rewrite `hA` using `[Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₁]`. Rewrite `hB` using `[Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₂]`. Take `⟨u, hu, e₁⟩` from `ZUnit.exists_of_span_eq (wedge_ne_zero f₁.1) hA`. Take `⟨u', hu', e₂⟩` from `ZUnit.exists_of_span_eq (wedge_ne_zero f₂.1) hB`.

Establish `hu0` using `hu.1`. Establish `hu0'` using `hu'.1`. Take `⟨v₀, hv₀, hf₁⟩` from `exists_valFam Z τ hβ hτ βF y hy hU h τ c₁ f₁`. Take `⟨w₀, hw₀, hf₂⟩` from `exists_valFam Z τ hβ hτ βF y hy hU h (ComplexEmbedding.conjugate τ) c₂ f₂`. Establish `hq : (u * α')⁻¹ / (u' * α')⁻¹ = u' * u⁻¹` using `by field_simp`.

Establish `hun : unitAt (Z.ξ₀ ≫ Y.j) ⟨_, h⟩ (u' * u⁻¹)` using `ZUnit.mul hu' (ZUnit.inv hu)`. Take `⟨r₀, hr₀⟩` from `RootHt.Pick.exists_valAt hun.2.1`. Take `⟨r₁, hr₁⟩` from `RootHt.Pick.exists_valAt hun.2.2`. Establish `hne : r₀ ≠ 0`. Introduce `h0`.

Establish `h1 : ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (1 : Z.Ω) (r₀ * r₁)`. Use `val_mul hr₀ hr₁` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel₀ hun.1]`. Then use the resulting hypothesis. Establish `h2 : ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (1 : Z.Ω) (1 : F)` using `⟨h, 1, map_one _, map_one (RootHt.Pick.valMap _)⟩`. Use `LieTangent.valAt_unique Z.gen h1 h2` as an intermediate fact.

Rewrite `this` using `[h0, MulZeroClass.zero_mul]`. Conclude with `zero_ne_one this`. Use `⟨h, c₁, c₂, (u * α')⁻¹, (u' * α')⁻¹, v₀, w₀, r₀, f₁, f₂, ?_, ?_, hv₀, hw₀, ⟨hy, hU, hf₁, hf₂⟩, ?_, hne⟩` and prove the remaining obligations. Rewrite using `[e₁, smul_smul, smul_smul, show (u * α')⁻¹ * (u : Z.Ω) * α' = 1 by field_simp, one_smul]`. Rewrite using `[e₂, smul_smul, smul_smul, show (u' * α')⁻¹ * (u' : Z.Ω) * α' = 1 by field_simp, one_smul]`.

Rewrite using `[hq]`. Conclude with `hr₀`.
-/
theorem exists_chart
    (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
    (hτ : τ (H.rt : E) = H.rt0)
    (hg : IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib)
    {F : Type} [Field F] (βF : c.F →+* F) (y : Sp F ⟶ Xo.XF c)
    (hy : y ≫ pullback.snd _ _ = spMap βF) (hU : Set.range y ⊆ U) :
    ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (c₁ : Fin D.p → Z.V) (c₂ : Fin D.q → Z.V) (α₀ κ₀ : Z.Ω)
      (v₀ : Vecs y D.p) (w₀ : Vecs y D.q) (r₀ : F),
      (Z.eig τ).IsFrameAt c₁ ⟨_, h⟩ ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt c₂ ⟨_, h⟩ ∧
      a = α₀ • exteriorPower.ιMulti Z.Ω D.p c₁ ∧ b = κ₀ • exteriorPower.ιMulti Z.Ω D.q c₂ ∧
      IsValFam Z y c₁ v₀ ∧ IsValFam Z y c₂ w₀ ∧ IsFramed U τ βF y v₀ w₀ ∧
      ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (α₀ / κ₀) r₀ ∧ r₀ ≠ 0 := by
  have h := spec_pt Z hU
  have hx := pt_mem_genFib Z y h
  obtain ⟨hvb₁, hvb₂, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨W₁, hW₁, c₁, -, hc₁⟩ := hvb₁ _ hx
  obtain ⟨W₂, hW₂, c₂, -, hc₂⟩ := hvb₂ _ hx
  have f₁ := hc₁ _ hx hW₁
  have f₂ := hc₂ _ hx hW₂
  obtain ⟨-, -, hco⟩ := hg
  obtain ⟨α', β', hα', -, hA, hB, e⟩ := hco _ hx
  rw [_root_.one_mul] at e
  subst e
  rw [Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₁] at hA
  rw [Lat.wedge_eq_span_of_isFrameAt _ _ _ _ _ _ _ _ f₂] at hB
  obtain ⟨u, hu, e₁⟩ := ZUnit.exists_of_span_eq (wedge_ne_zero f₁.1) hA
  obtain ⟨u', hu', e₂⟩ := ZUnit.exists_of_span_eq (wedge_ne_zero f₂.1) hB
  have hu0 := hu.1
  have hu0' := hu'.1
  obtain ⟨v₀, hv₀, hf₁⟩ := exists_valFam Z τ hβ hτ βF y hy hU h τ c₁ f₁
  obtain ⟨w₀, hw₀, hf₂⟩ := exists_valFam Z τ hβ hτ βF y hy hU h (ComplexEmbedding.conjugate τ) c₂ f₂
  have hq : (u * α')⁻¹ / (u' * α')⁻¹ = u' * u⁻¹ := by field_simp
  have hun : unitAt (Z.ξ₀ ≫ Y.j) ⟨_, h⟩ (u' * u⁻¹) := ZUnit.mul hu' (ZUnit.inv hu)
  obtain ⟨r₀, hr₀⟩ := RootHt.Pick.exists_valAt hun.2.1
  obtain ⟨r₁, hr₁⟩ := RootHt.Pick.exists_valAt hun.2.2
  have hne : r₀ ≠ 0 := by
    intro h0
    have h1 : ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (1 : Z.Ω) (r₀ * r₁) := by
      have := val_mul hr₀ hr₁
      rwa [mul_inv_cancel₀ hun.1] at this
    have h2 : ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (1 : Z.Ω) (1 : F) := ⟨h, 1, map_one _, map_one (RootHt.Pick.valMap _)⟩
    have := LieTangent.valAt_unique Z.gen h1 h2
    rw [h0, MulZeroClass.zero_mul] at this
    exact zero_ne_one this
  refine ⟨h, c₁, c₂, (u * α')⁻¹, (u' * α')⁻¹, v₀, w₀, r₀, f₁, f₂, ?_, ?_, hv₀, hw₀, ⟨hy, hU, hf₁, hf₂⟩, ?_, hne⟩
  · rw [e₁, smul_smul, smul_smul, show (u * α')⁻¹ * (u : Z.Ω) * α' = 1 by field_simp, one_smul]
  · rw [e₂, smul_smul, smul_smul, show (u' * α')⁻¹ * (u' : Z.Ω) * α' = 1 by field_simp, one_smul]
  · rw [hq]
    exact hr₀

variable {Z τ a b}

/- English proof (translation)
Establish `hα : α ≠ 0` using `by rintro rfl; exact ha (by rw [ea, zero_smul])`. Establish `hκ : κ ≠ 0` using `by rintro rfl; exact hb (by rw [eb, zero_smul])`. Establish `hα₀ : α₀ ≠ 0` using `by rintro rfl; exact ha (by rw [ea₀, zero_smul])`. Establish `hκ₀ : κ₀ ≠ 0` using `by rintro rfl; exact hb (by rw [eb₀, zero_smul])`. Establish `w₁ : exteriorPower.ιMulti Z.Ω D.p b₁ = (α₀ / α) • exteriorPower.ιMulti Z.Ω D.p c₁`.

Rewrite using `[div_eq_inv_mul, mul_smul, ← ea₀, ea, smul_smul, inv_mul_cancel₀ hα, one_smul]`. Establish `w₂ : exteriorPower.ιMulti Z.Ω D.q b₂ = (κ₀ / κ) • exteriorPower.ιMulti Z.Ω D.q c₂`. Rewrite using `[div_eq_inv_mul, mul_smul, ← eb₀, eb, smul_smul, inv_mul_cancel₀ hκ, one_smul]`. Take `⟨A, hA, dA, vA⟩` from `expand Z h τ _ f₁ hv₀ hv hfr₀.2.2.1 hfr.2.2.1 (div_ne_zero hα₀ hα) w₁`. Take `⟨B, hB, dB, vB⟩` from `expand Z h _ _ f₂ hw₀ hw hfr₀.2.2.2 hfr.2.2.2 (div_ne_zero hκ₀ hκ) w₂`.

Use `⟨A, B, hA, hB, dA, dB, ?_⟩` and prove the remaining obligations. Use `val_mul (val_mul hr₀ vB) (val_inv vA dA)` as an intermediate fact. Establish `e : α₀ / κ₀ * (κ₀ / κ) * (α₀ / α)⁻¹ = α / κ` using `by field_simp`. Rewrite `this` using `[e]`. Rewrite using `[div_eq_mul_inv (r₀ * B.det)]`.

Conclude with `this`.
-/
theorem vs_chart {F : Type} [Field F] {βF : c.F →+* F} {y : Sp F ⟶ Xo.XF c}
    {h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)} {c₁ : Fin D.p → Z.V} {c₂ : Fin D.q → Z.V} {α₀ κ₀ : Z.Ω}
    {v₀ v : Vecs y D.p} {w₀ w : Vecs y D.q} {r₀ : F} {b₁ : Fin D.p → Z.V} {b₂ : Fin D.q → Z.V} {α κ : Z.Ω}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (f₁ : (Z.eig τ).IsFrameAt c₁ ⟨_, h⟩) (f₂ : (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt c₂ ⟨_, h⟩)
    (ea₀ : a = α₀ • exteriorPower.ιMulti Z.Ω D.p c₁) (eb₀ : b = κ₀ • exteriorPower.ιMulti Z.Ω D.q c₂)
    (hv₀ : IsValFam Z y c₁ v₀) (hw₀ : IsValFam Z y c₂ w₀) (hfr₀ : IsFramed U τ βF y v₀ w₀)
    (hr₀ : ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (α₀ / κ₀) r₀) (hfr : IsFramed U τ βF y v w)
    (ea : a = α • exteriorPower.ιMulti Z.Ω D.p b₁) (eb : b = κ • exteriorPower.ιMulti Z.Ω D.q b₂)
    (hv : IsValFam Z y b₁ v) (hw : IsValFam Z y b₂ w) :
    ∃ (A : Matrix (Fin D.p) (Fin D.p) F) (B : Matrix (Fin D.q) (Fin D.q) F), (∀ i, IsComb (A i) v₀ (v i)) ∧
      (∀ j, IsComb (B j) w₀ (w j)) ∧ A.det ≠ 0 ∧ B.det ≠ 0 ∧
      ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (α / κ) (r₀ * B.det / A.det) := by
  have hα : α ≠ 0 := by rintro rfl; exact ha (by rw [ea, zero_smul])
  have hκ : κ ≠ 0 := by rintro rfl; exact hb (by rw [eb, zero_smul])
  have hα₀ : α₀ ≠ 0 := by rintro rfl; exact ha (by rw [ea₀, zero_smul])
  have hκ₀ : κ₀ ≠ 0 := by rintro rfl; exact hb (by rw [eb₀, zero_smul])
  have w₁ : exteriorPower.ιMulti Z.Ω D.p b₁ = (α₀ / α) • exteriorPower.ιMulti Z.Ω D.p c₁ := by
    rw [div_eq_inv_mul, mul_smul, ← ea₀, ea, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have w₂ : exteriorPower.ιMulti Z.Ω D.q b₂ = (κ₀ / κ) • exteriorPower.ιMulti Z.Ω D.q c₂ := by
    rw [div_eq_inv_mul, mul_smul, ← eb₀, eb, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  obtain ⟨A, hA, dA, vA⟩ := expand Z h τ _ f₁ hv₀ hv hfr₀.2.2.1 hfr.2.2.1 (div_ne_zero hα₀ hα) w₁
  obtain ⟨B, hB, dB, vB⟩ := expand Z h _ _ f₂ hw₀ hw hfr₀.2.2.2 hfr.2.2.2 (div_ne_zero hκ₀ hκ) w₂
  refine ⟨A, B, hA, hB, dA, dB, ?_⟩
  have := val_mul (val_mul hr₀ vB) (val_inv vA dA)
  have e : α₀ / κ₀ * (κ₀ / κ) * (α₀ / α)⁻¹ = α / κ := by field_simp
  rw [e] at this
  rw [div_eq_mul_inv (r₀ * B.det)]
  exact this

variable (hβ : Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a)
  (hτ : τ (H.rt : E) = H.rt0)
  (hg : IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib)
include hβ hτ hg

/- English proof (translation)
Take `⟨βF, b₁, b₂, α, κ, hfr, ea, eb, hv, hw, hr⟩` from `h`. Take `⟨βF', b₁', b₂', α', κ', hfr', ea', eb', hv', hw', hr'⟩` from `h'`. Take `rfl : βF = βF'` from `spMap_inj (hfr.1.symm.trans hfr'.1)`. Take `⟨h0, c₁, c₂, α₀, κ₀, v₀, w₀, r₀, f₁, f₂, ea₀, eb₀, hv₀, hw₀, hfr₀, hr₀, -⟩` from `exists_chart Z τ a b hβ hτ hg βF y hfr.1 hfr.2.1`. Take `⟨A₁, B₁, a₁, b₁c, d₁, e₁, l₁⟩` from `vs_chart hg.1 hg.2.1 f₁ f₂ ea₀ eb₀ hv₀ hw₀ hfr₀ hr₀ hfr ea eb hv hw`.

Take `⟨A₂, B₂, a₂, b₂c, d₂, e₂, l₂⟩` from `vs_chart hg.1 hg.2.1 f₁ f₂ ea₀ eb₀ hv₀ hw₀ hfr₀ hr₀ hfr' ea' eb' hv' hw'`. Establish `er` using `LieTangent.valAt_unique Z.gen hr l₁`. Establish `er'` using `LieTangent.valAt_unique Z.gen hr' l₂`. Establish `hA₂ : A₂ = A * A₁`. Use extensionality with `i j`.

Conclude with `congrFun ((hfr₀.2.2.1.2 _ (hfr'.2.2.1.1 i)).unique (a₂ i) (comb_mul (fun k => (hfr₀.2.2.1.1 k).1) a₁ hA i)) j`. Establish `hB₂ : B₂ = B * B₁`. Use extensionality with `i j`. Conclude with `congrFun ((hfr₀.2.2.2.2 _ (hfr'.2.2.2.1 i)).unique (b₂c i) (comb_mul (fun k => (hfr₀.2.2.2.1 k).1) b₁c hB i)) j`. Substitute `hA₂ hB₂` using the available equality.

Rewrite `d₂`, `e₂`, `er'` using `[Matrix.det_mul]`. Rewrite `er'` using `[Matrix.det_mul]`. Establish `dA` using `left_ne_zero_of_mul d₂`. Rewrite using `[er, er']`. Clear the denominators using the available nonvanishing facts.
-/
theorem rat_cocycle {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c} {v v' : Vecs y D.p} {w w' : Vecs y D.q} {r r' : F}
    {A : Matrix (Fin D.p) (Fin D.p) F} {B : Matrix (Fin D.q) (Fin D.q) F} (h : IsRat Z τ a b y v w r)
    (h' : IsRat Z τ a b y v' w' r') (hA : ∀ i, IsComb (A i) v (v' i)) (hB : ∀ j, IsComb (B j) w (w' j)) :
    r' * A.det = r * B.det := by
  obtain ⟨βF, b₁, b₂, α, κ, hfr, ea, eb, hv, hw, hr⟩ := h
  obtain ⟨βF', b₁', b₂', α', κ', hfr', ea', eb', hv', hw', hr'⟩ := h'
  obtain rfl : βF = βF' := spMap_inj (hfr.1.symm.trans hfr'.1)
  obtain ⟨h0, c₁, c₂, α₀, κ₀, v₀, w₀, r₀, f₁, f₂, ea₀, eb₀, hv₀, hw₀, hfr₀, hr₀, -⟩ :=
    exists_chart Z τ a b hβ hτ hg βF y hfr.1 hfr.2.1
  obtain ⟨A₁, B₁, a₁, b₁c, d₁, e₁, l₁⟩ := vs_chart hg.1 hg.2.1 f₁ f₂ ea₀ eb₀ hv₀ hw₀ hfr₀ hr₀ hfr ea eb hv hw
  obtain ⟨A₂, B₂, a₂, b₂c, d₂, e₂, l₂⟩ := vs_chart hg.1 hg.2.1 f₁ f₂ ea₀ eb₀ hv₀ hw₀ hfr₀ hr₀ hfr' ea' eb' hv' hw'
  have er := LieTangent.valAt_unique Z.gen hr l₁
  have er' := LieTangent.valAt_unique Z.gen hr' l₂
  have hA₂ : A₂ = A * A₁ := by
    ext i j
    exact congrFun ((hfr₀.2.2.1.2 _ (hfr'.2.2.1.1 i)).unique (a₂ i)
      (comb_mul (fun k => (hfr₀.2.2.1.1 k).1) a₁ hA i)) j
  have hB₂ : B₂ = B * B₁ := by
    ext i j
    exact congrFun ((hfr₀.2.2.2.2 _ (hfr'.2.2.2.1 i)).unique (b₂c i)
      (comb_mul (fun k => (hfr₀.2.2.2.1 k).1) b₁c hB i)) j
  subst hA₂ hB₂
  rw [Matrix.det_mul] at d₂ e₂ er'
  rw [Matrix.det_mul] at er'
  have dA := left_ne_zero_of_mul d₂
  rw [er, er']
  field_simp

/- English proof (translation)
Take `⟨v₀, w₀, r₀, A, B, hR, hA, hB, hd, e⟩` from `h`. Take `⟨v₁, w₁, r₁, A₁, B₁, hR₁, hA₁, hB₁, hd₁, e₁⟩` from `h'`. Establish `hR'` using `hR`. Establish `hR₁'` using `hR₁`. Take `⟨βF, -, -, -, -, hfr, -⟩` from `hR'`.

Take `⟨βF', -, -, -, -, hfr₁, -⟩` from `hR₁'`. Take `rfl : βF = βF'` from `spMap_inj (hfr.1.symm.trans hfr₁.1)`. Establish `: ∀ i, ∃ cf, IsComb cf v₀ (v₁ i)` using `fun i => (hfr.2.2.1.2 _ (hfr₁.2.2.1.1 i)).exists`. Use `choose C hC using this`. Establish `: ∀ i, ∃ cf, IsComb cf w₀ (w₁ i)` using `fun i => (hfr.2.2.2.2 _ (hfr₁.2.2.2.1 i)).exists`.

Use `choose P hP using this`. Establish `K` using `rat_cocycle hβ hτ hg (A := Matrix.of C) (B := Matrix.of P) hR hR₁ hC hP`. Establish `eA : A = A₁ * Matrix.of C`. Use extensionality with `i j`. Conclude with `congrFun ((hfr.2.2.1.2 _ (comb_eig _ _ hfr.2.2.1.1 (hA i))).unique (hA i) (comb_mul (fun k => (hfr.2.2.1.1 k).1) hC hA₁ i)) j`.

Establish `eB : B = B₁ * Matrix.of P`. Use extensionality with `i j`. Conclude with `congrFun ((hfr.2.2.2.2 _ (comb_eig _ _ hfr.2.2.2.1 (hB i))).unique (hB i) (comb_mul (fun k => (hfr.2.2.2.1 k).1) hP hB₁ i)) j`. Substitute `eA eB` using the available equality. Rewrite `hd`, `e` using `[Matrix.det_mul]`.

Rewrite `e` using `[Matrix.det_mul]`. Use `mul_right_cancel₀ hd ?_` and prove the remaining obligations. Take the linear combination `e - (Matrix.of C).det * e₁ - B₁.det * K`.
-/
theorem isGen_unique {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c} {v : Vecs y D.p} {w : Vecs y D.q} {r r' : F}
    (h : IsGen Z τ a b y v w r) (h' : IsGen Z τ a b y v w r') : r = r' := by
  obtain ⟨v₀, w₀, r₀, A, B, hR, hA, hB, hd, e⟩ := h
  obtain ⟨v₁, w₁, r₁, A₁, B₁, hR₁, hA₁, hB₁, hd₁, e₁⟩ := h'
  have hR' := hR
  have hR₁' := hR₁
  obtain ⟨βF, -, -, -, -, hfr, -⟩ := hR'
  obtain ⟨βF', -, -, -, -, hfr₁, -⟩ := hR₁'
  obtain rfl : βF = βF' := spMap_inj (hfr.1.symm.trans hfr₁.1)
  have : ∀ i, ∃ cf, IsComb cf v₀ (v₁ i) := fun i => (hfr.2.2.1.2 _ (hfr₁.2.2.1.1 i)).exists
  choose C hC using this
  have : ∀ i, ∃ cf, IsComb cf w₀ (w₁ i) := fun i => (hfr.2.2.2.2 _ (hfr₁.2.2.2.1 i)).exists
  choose P hP using this
  have K := rat_cocycle hβ hτ hg (A := Matrix.of C) (B := Matrix.of P) hR hR₁ hC hP
  have eA : A = A₁ * Matrix.of C := by
    ext i j
    exact congrFun ((hfr.2.2.1.2 _ (comb_eig _ _ hfr.2.2.1.1 (hA i))).unique (hA i)
      (comb_mul (fun k => (hfr.2.2.1.1 k).1) hC hA₁ i)) j
  have eB : B = B₁ * Matrix.of P := by
    ext i j
    exact congrFun ((hfr.2.2.2.2 _ (comb_eig _ _ hfr.2.2.2.1 (hB i))).unique (hB i)
      (comb_mul (fun k => (hfr.2.2.2.1 k).1) hP hB₁ i)) j
  subst eA eB
  rw [Matrix.det_mul] at hd e
  rw [Matrix.det_mul] at e
  refine mul_right_cancel₀ hd ?_
  linear_combination e - (Matrix.of C).det * e₁ - B₁.det * K

/- English proof (translation)
Establish `hex : ∃ r, IsGen Z τ a b y v w r` using `⟨r, h⟩`. Unfold `repFn`. Rewrite using `[dif_pos hex]`. Conclude with `isGen_unique hβ hτ hg hex.choose_spec h`.
-/
theorem repFn_eq {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c} {v : Vecs y D.p} {w : Vecs y D.q} {r : F}
    (h : IsGen Z τ a b y v w r) : repFn Z τ a b F y v w = r := by
  have hex : ∃ r, IsGen Z τ a b y v w r := ⟨r, h⟩
  unfold repFn
  rw [dif_pos hex]
  exact isGen_unique hβ hτ hg hex.choose_spec h

/- English proof (translation)
Take `⟨h0, c₁, c₂, α₀, κ₀, v₀, w₀, r₀, f₁, f₂, ea₀, eb₀, hv₀, hw₀, hfr₀, hr₀, hne⟩` from `exists_chart Z τ a b hβ hτ hg βF y hfr.1 hfr.2.1`. Establish `: ∀ i, ∃ cf, IsComb cf v₀ (v i)` using `fun i => (hfr₀.2.2.1.2 _ (hfr.2.2.1.1 i)).exists`. Use `choose A hA using this`. Establish `: ∀ i, ∃ cf, IsComb cf w₀ (w i)` using `fun i => (hfr₀.2.2.2.2 _ (hfr.2.2.2.1 i)).exists`. Use `choose B hB using this`.

Establish `dA : (Matrix.of A).det ≠ 0` using `frame_det hfr₀.2.2.1 hfr.2.2.1 hA`. Establish `dB : (Matrix.of B).det ≠ 0` using `frame_det hfr₀.2.2.2 hfr.2.2.2 hB`. Use `⟨r₀ * (Matrix.of B).det / (Matrix.of A).det, div_ne_zero (mul_ne_zero hne dB) dA, v₀, w₀, r₀, Matrix.of A, Matrix.of B, ⟨βF, c₁, c₂, α₀, κ₀, hfr₀, ea₀, eb₀, hv₀, hw₀, hr₀⟩, hA, hB, dA, ?_⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_isGen {F : Type} [Field F] {βF : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v : Vecs y D.p}
    {w : Vecs y D.q} (hfr : IsFramed U τ βF y v w) : ∃ r, r ≠ 0 ∧ IsGen Z τ a b y v w r := by
  obtain ⟨h0, c₁, c₂, α₀, κ₀, v₀, w₀, r₀, f₁, f₂, ea₀, eb₀, hv₀, hw₀, hfr₀, hr₀, hne⟩ :=
    exists_chart Z τ a b hβ hτ hg βF y hfr.1 hfr.2.1
  have : ∀ i, ∃ cf, IsComb cf v₀ (v i) := fun i => (hfr₀.2.2.1.2 _ (hfr.2.2.1.1 i)).exists
  choose A hA using this
  have : ∀ i, ∃ cf, IsComb cf w₀ (w i) := fun i => (hfr₀.2.2.2.2 _ (hfr.2.2.2.1 i)).exists
  choose B hB using this
  have dA : (Matrix.of A).det ≠ 0 := frame_det hfr₀.2.2.1 hfr.2.2.1 hA
  have dB : (Matrix.of B).det ≠ 0 := frame_det hfr₀.2.2.2 hfr.2.2.2 hB
  refine ⟨r₀ * (Matrix.of B).det / (Matrix.of A).det, div_ne_zero (mul_ne_zero hne dB) dA, v₀, w₀, r₀, Matrix.of A,
    Matrix.of B, ⟨βF, c₁, c₂, α₀, κ₀, hfr₀, ea₀, eb₀, hv₀, hw₀, hr₀⟩, hA, hB, dA, ?_⟩
  field_simp

omit hβ hτ hg in
/- English proof (translation)
Take `⟨βF, b₁, b₂, α, κ, hfr, ea, eb, hv, hw, hr⟩` from `h`. Use `haveI : Smooth Xo.univ.t.G.hom := Xo.univ.t.semi.smooth`. Establish `hx : spMap f ≫ under y = under (spMap f ≫ y)` using `(Category.assoc _ _ _).symm`. Use `⟨f.comp βF, b₁, b₂, α, κ, ⟨?_, ?_, ?_, ?_⟩, ea, eb, valFam_base Z f rfl hv' hv, valFam_base Z f rfl hw' hw, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, hfr.1]`.

Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Introduce and unpack `_ ⟨p, rfl⟩`. Rewrite using `[Scheme.Hom.comp_apply]`. Conclude with `hfr.2.1 (Set.mem_range_self _)`. Rewrite using `[RingHom.comp_assoc]`.

Conclude with `eigFrame_base Xo.univ.t.act _ f hx hv' hfr.2.2.1`. Rewrite using `[RingHom.comp_assoc]`. Conclude with `eigFrame_base Xo.univ.t.act _ f hx hw' hfr.2.2.2`. Use `LieTangent.valAt_base Z.gen f hr` as an intermediate fact. Rewrite `this` using `[← Category.assoc]`. Then use the resulting hypothesis.
-/
theorem rat_base {F F' : Type} [Field F] [Field F'] (f : F →+* F') {y : Sp F ⟶ Xo.XF c}
    {v : Vecs y D.p} {w : Vecs y D.q} {v' : Vecs (spMap f ≫ y) D.p} {w' : Vecs (spMap f ≫ y) D.q} {r : F}
    (hv' : ∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left)
    (hw' : ∀ i, (w' i).left = spMap (dualMap f) ≫ (w i).left) (h : IsRat Z τ a b y v w r) :
    IsRat Z τ a b (spMap f ≫ y) v' w' (f r) := by
  obtain ⟨βF, b₁, b₂, α, κ, hfr, ea, eb, hv, hw, hr⟩ := h
  haveI : Smooth Xo.univ.t.G.hom := Xo.univ.t.semi.smooth
  have hx : spMap f ≫ under y = under (spMap f ≫ y) := (Category.assoc _ _ _).symm
  refine ⟨f.comp βF, b₁, b₂, α, κ, ⟨?_, ?_, ?_, ?_⟩, ea, eb, valFam_base Z f rfl hv' hv, valFam_base Z f rfl hw' hw, ?_⟩
  · rw [Category.assoc, hfr.1]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hfr.2.1 (Set.mem_range_self _)
  · rw [RingHom.comp_assoc]
    exact eigFrame_base Xo.univ.t.act _ f hx hv' hfr.2.2.1
  · rw [RingHom.comp_assoc]
    exact eigFrame_base Xo.univ.t.act _ f hx hw' hfr.2.2.2
  · have := LieTangent.valAt_base Z.gen f hr
    rwa [← Category.assoc] at this

omit hβ hτ hg in
/- English proof (translation)
Take `⟨v₀, w₀, r₀, A, B, hR, hA, hB, hd, e⟩` from `h`. Establish `hx : spMap f ≫ under y = under (spMap f ≫ y)` using `(Category.assoc _ _ _).symm`. Establish `p₁ : ∀ i, ((LieTangent.epsBase f hx ≫ v₀ i : epsAt (under (spMap f ≫ y)) ⟶ _)).left = spMap (dualMap f) ≫ (v₀ i).left` using `fun _ => rfl`. Establish `p₂ : ∀ i, ((LieTangent.epsBase f hx ≫ w₀ i : epsAt (under (spMap f ≫ y)) ⟶ _)).left = spMap (dualMap f) ≫ (w₀ i).left` using `fun _ => rfl`. Use `⟨fun i => LieTangent.epsBase f hx ≫ v₀ i, fun i => LieTangent.epsBase f hx ≫ w₀ i, f r₀, f.mapMatrix A, f.mapMatrix B, rat_base f p₁ p₂ hR, fun i => comb_base f hx p₁ (hv' i) (hA i), fun i => comb_base f hx p₂ (hw' i) (hB i), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← RingHom.map_det]`. Conclude with `(map_ne_zero f).2 hd`. Rewrite using `[← RingHom.map_det, ← RingHom.map_det, ← map_mul, ← map_mul, e]`.
-/
theorem isGen_base {F F' : Type} [Field F] [Field F'] (f : F →+* F') {y : Sp F ⟶ Xo.XF c}
    {v : Vecs y D.p} {w : Vecs y D.q} {v' : Vecs (spMap f ≫ y) D.p} {w' : Vecs (spMap f ≫ y) D.q} {r : F}
    (hv' : ∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left)
    (hw' : ∀ i, (w' i).left = spMap (dualMap f) ≫ (w i).left) (h : IsGen Z τ a b y v w r) :
    IsGen Z τ a b (spMap f ≫ y) v' w' (f r) := by
  obtain ⟨v₀, w₀, r₀, A, B, hR, hA, hB, hd, e⟩ := h
  have hx : spMap f ≫ under y = under (spMap f ≫ y) := (Category.assoc _ _ _).symm
  have p₁ : ∀ i, ((LieTangent.epsBase f hx ≫ v₀ i : epsAt (under (spMap f ≫ y)) ⟶ _)).left =
    spMap (dualMap f) ≫ (v₀ i).left := fun _ => rfl
  have p₂ : ∀ i, ((LieTangent.epsBase f hx ≫ w₀ i : epsAt (under (spMap f ≫ y)) ⟶ _)).left =
    spMap (dualMap f) ≫ (w₀ i).left := fun _ => rfl
  refine ⟨fun i => LieTangent.epsBase f hx ≫ v₀ i, fun i => LieTangent.epsBase f hx ≫ w₀ i, f r₀, f.mapMatrix A,
    f.mapMatrix B, rat_base f p₁ p₂ hR, fun i => comb_base f hx p₁ (hv' i) (hA i),
    fun i => comb_base f hx p₂ (hw' i) (hB i), ?_, ?_⟩
  · rw [← RingHom.map_det]
    exact (map_ne_zero f).2 hd
  · rw [← RingHom.map_det, ← RingHom.map_det, ← map_mul, ← map_mul, e]

/- English proof (translation)
Take `⟨r, hr, h⟩` from `exists_isGen hβ hτ hg hfr`. Rewrite using `[repFn_eq hβ hτ hg h]` and apply the resulting hypothesis. Use `chg F _ βF y v w v' w' A B hfr hfr' hA hB := by`. Take `⟨r, -, h⟩` from `exists_isGen hβ hτ hg hfr`. Take `⟨v₀, w₀, r₀, A₀, B₀, hR, a₀, b₀, d₀, e₀⟩` from `id h`.

Establish `hR'` using `hR`. Take `⟨βF', -, -, -, -, hfr₀, -⟩` from `hR'`. Take `rfl : βF = βF'` from `spMap_inj (hfr.1.symm.trans hfr₀.1)`. Establish `dA : A.det ≠ 0` using `frame_det hfr.2.2.1 hfr'.2.2.1 hA`. Establish `h' : IsGen Z τ a b y v' w' (r₀ * (B * B₀).det / (A * A₀).det)` using `⟨v₀, w₀, r₀, A * A₀, B * B₀, hR, comb_mul (fun k => (hfr₀.2.2.1.1 k).1) a₀ hA, comb_mul (fun k => (hfr₀.2.2.2.1 k).1) b₀ hB, by rw [Matrix.det_mul]; exact mul_ne_zero dA d₀, div_mul_cancel₀ _ (by rw [Matrix.det_mul]; exact mul_ne_zero dA d₀)⟩`.

Rewrite using `[repFn_eq hβ hτ hg h, repFn_eq hβ hτ hg h', Matrix.det_mul, Matrix.det_mul]`. Establish `: r = r₀ * B₀.det / A₀.det` using `by field_simp; exact e₀`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Use `nat F F' _ _ f βF y v w y' v' w' hfr hy hv hw := by`.

Substitute `hy` using the available equality. Take `⟨r, -, h⟩` from `exists_isGen hβ hτ hg hfr`. Rewrite using `[repFn_eq hβ hτ hg h, repFn_eq hβ hτ hg (isGen_base f hv hw h)]`.
-/
theorem isLineFn_repFn : IsLineFn U τ (repFn Z τ a b) where
  ne F _ βF y v w hfr := by
    obtain ⟨r, hr, h⟩ := exists_isGen hβ hτ hg hfr
    rwa [repFn_eq hβ hτ hg h]
  chg F _ βF y v w v' w' A B hfr hfr' hA hB := by
    obtain ⟨r, -, h⟩ := exists_isGen hβ hτ hg hfr
    obtain ⟨v₀, w₀, r₀, A₀, B₀, hR, a₀, b₀, d₀, e₀⟩ := id h
    have hR' := hR
    obtain ⟨βF', -, -, -, -, hfr₀, -⟩ := hR'
    obtain rfl : βF = βF' := spMap_inj (hfr.1.symm.trans hfr₀.1)
    have dA : A.det ≠ 0 := frame_det hfr.2.2.1 hfr'.2.2.1 hA
    have h' : IsGen Z τ a b y v' w' (r₀ * (B * B₀).det / (A * A₀).det) :=
      ⟨v₀, w₀, r₀, A * A₀, B * B₀, hR, comb_mul (fun k => (hfr₀.2.2.1.1 k).1) a₀ hA,
        comb_mul (fun k => (hfr₀.2.2.2.1 k).1) b₀ hB, by rw [Matrix.det_mul]; exact mul_ne_zero dA d₀,
        div_mul_cancel₀ _ (by rw [Matrix.det_mul]; exact mul_ne_zero dA d₀)⟩
    rw [repFn_eq hβ hτ hg h, repFn_eq hβ hτ hg h', Matrix.det_mul, Matrix.det_mul]
    have : r = r₀ * B₀.det / A₀.det := by field_simp; exact e₀
    rw [this]
    field_simp
  nat F F' _ _ f βF y v w y' v' w' hfr hy hv hw := by
    subst hy
    obtain ⟨r, -, h⟩ := exists_isGen hβ hτ hg hfr
    rw [repFn_eq hβ hτ hg h, repFn_eq hβ hτ hg (isGen_base f hv hw h)]

/- English proof (translation)
Introduce `F _ βF y v w b₁ b₂ α κ hfr ea eb hv hw`. Take `⟨h0, c₁, c₂, α₀, κ₀, v₀, w₀, r₀, f₁, f₂, ea₀, eb₀, hv₀, hw₀, hfr₀, hr₀, -⟩` from `exists_chart Z τ a b hβ hτ hg βF y hfr.1 hfr.2.1`. Take `⟨A, B, hA, hB, dA, dB, l⟩` from `vs_chart hg.1 hg.2.1 f₁ f₂ ea₀ eb₀ hv₀ hw₀ hfr₀ hr₀ hfr ea eb hv hw`. Establish `h : IsGen Z τ a b y v w (r₀ * B.det / A.det)` using `⟨v₀, w₀, r₀, A, B, ⟨βF, c₁, c₂, α₀, κ₀, hfr₀, ea₀, eb₀, hv₀, hw₀, hr₀⟩, hA, hB, dA, div_mul_cancel₀ _ dA⟩`. Rewrite using `[repFn_eq hβ hτ hg h]`.

Conclude with `l`.
-/
theorem represents_repFn : Represents Y U τ Z.M a b (repFn Z τ a b) := by
  intro F _ βF y v w b₁ b₂ α κ hfr ea eb hv hw
  obtain ⟨h0, c₁, c₂, α₀, κ₀, v₀, w₀, r₀, f₁, f₂, ea₀, eb₀, hv₀, hw₀, hfr₀, hr₀, -⟩ :=
    exists_chart Z τ a b hβ hτ hg βF y hfr.1 hfr.2.1
  obtain ⟨A, B, hA, hB, dA, dB, l⟩ := vs_chart hg.1 hg.2.1 f₁ f₂ ea₀ eb₀ hv₀ hw₀ hfr₀ hr₀ hfr ea eb hv hw
  have h : IsGen Z τ a b y v w (r₀ * B.det / A.det) :=
    ⟨v₀, w₀, r₀, A, B, ⟨βF, c₁, c₂, α₀, κ₀, hfr₀, ea₀, eb₀, hv₀, hw₀, hr₀⟩, hA, hB, dA, div_mul_cancel₀ _ dA⟩
  rw [repFn_eq hβ hτ hg h]
  exact l

end Main

end GlobalTheory.CompanionTheory.Ar.Flat.Rep

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c O _ β Y U Z τ a b hβ hτ hg`. Conclude with `⟨Rep.repFn Z τ a b, Rep.isLineFn_repFn hβ hτ hg, Rep.represents_repFn hβ hτ hg⟩`.
-/
theorem exists_frameFn_of_gen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → IsLineGenOn (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q a b Z.genFib → ∃ φ : FrameFn Xo c, IsLineFn U τ φ ∧ Represents Y U τ Z.M a b φ := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ a b hβ hτ hg
  exact ⟨Rep.repFn Z τ a b, Rep.isLineFn_repFn hβ hτ hg, Rep.represents_repFn hβ hτ hg⟩

end GlobalTheory.CompanionTheory.Ar.Flat
