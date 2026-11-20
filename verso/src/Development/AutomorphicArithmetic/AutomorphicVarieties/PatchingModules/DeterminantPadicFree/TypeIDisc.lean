import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.GGram
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DToDetOfRep
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

open UpperTheory.V.CA in
/- English proof (translation)
Establish `h1` using `((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1`. Rewrite `h1` using `[MonoidAlgebra.mapRingHom_single, map_one, h]`. Establish `h2` using `(d_toDet (GDet.ofRep ρ) (MonoidAlgebra.single g 1)).2.2.1`. Rewrite `h2` using `[d_toDet_ofRep.1, (d_ofRep _ _ _).2.2.1 hn]`. Establish `h3 : GDet.repAlg ρ K (MonoidAlgebra.single g 1) = ρ g`.

Use extensionality with `i j`. Simplify using `[GDet.repAlg]`. Rewrite `h2` using `[h3]`. Conclude with `h1.symm.trans h2.symm`.
-/
private theorem tr_of_map {n : ℕ} {A G K : Type} [CommRing A] [Group G] [CommRing K] (hn : 1 ≤ n)
    (D : GDet n A G) (f : A →+* K) (ρ : G →* Matrix (Fin n) (Fin n) K) (h : D.map f = GDet.ofRep ρ) (g : G) :
    f (D.tr (MonoidAlgebra.single g 1)) = (ρ g).trace := by
  have h1 := ((d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)).2 1
  rw [MonoidAlgebra.mapRingHom_single, map_one, h] at h1
  have h2 := (d_toDet (GDet.ofRep ρ) (MonoidAlgebra.single g 1)).2.2.1
  rw [d_toDet_ofRep.1, (d_ofRep _ _ _).2.2.1 hn] at h2
  have h3 : GDet.repAlg ρ K (MonoidAlgebra.single g 1) = ρ g := by
    ext i j; simp [GDet.repAlg]
  rw [h3] at h2
  exact h1.symm.trans h2.symm

/- English proof (translation)
Establish `h1 : ∀ Z ∈ Submodule.span A S, (algebraMap A L).mapMatrix Z ∈ Submodule.span L ((algebraMap A L).mapMatrix '' S)`. Introduce `Z hZ`. Proceed by induction on `hZ using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`. Consider the case `smul c y _ hy`. Establish `: (algebraMap A L).mapMatrix (c • y) = algebraMap A L c • (algebraMap A L).mapMatrix y`. Use extensionality with `i j`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ hy`. Establish `h2 : ∀ Z : Matrix (Fin n) (Fin n) A, (algebraMap A L).mapMatrix Z ∈ Submodule.span L ((algebraMap A L).mapMatrix '' S)`. Introduce `Z`.

Take `⟨s, hs⟩` from `hS Z`. Establish `h` using `h1 _ hs`. Establish `e : (algebraMap A L).mapMatrix (t ^ s • Z) = algebraMap A L t ^ s • (algebraMap A L).mapMatrix Z`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Rewrite `h` using `[e]`. Conclude with `(Submodule.smul_mem_iff _ (pow_ne_zero s ht)).1 h`. Rewrite using `[eq_top_iff]`. Introduce `Z _`. Rewrite using `[Matrix.matrix_eq_sum_single Z]`.

Use `Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Establish `e : Matrix.single i j (Z i j) = Z i j • (algebraMap A L).mapMatrix (Matrix.single i j (1 : A))`. Use extensionality with `a b`. Apply the tactic sequence `by_cases h : i = a ∧ j = b <;> simp [Matrix.single_apply, h]`. Rewrite using `[e]`.

Conclude with `Submodule.smul_mem _ _ (h2 _)`.
-/
private theorem span_top {n : ℕ} {A L : Type} [CommRing A] [Field L] [Algebra A L] (t : A)
    (ht : algebraMap A L t ≠ 0) (S : Set (Matrix (Fin n) (Fin n) A))
    (hS : ∀ Z, ∃ s : ℕ, t ^ s • Z ∈ Submodule.span A S) :
    Submodule.span L ((algebraMap A L).mapMatrix '' S) = ⊤ := by
  have h1 : ∀ Z ∈ Submodule.span A S, (algebraMap A L).mapMatrix Z ∈
      Submodule.span L ((algebraMap A L).mapMatrix '' S) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have : (algebraMap A L).mapMatrix (c • y) = algebraMap A L c • (algebraMap A L).mapMatrix y := by
        ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ hy
  have h2 : ∀ Z : Matrix (Fin n) (Fin n) A, (algebraMap A L).mapMatrix Z ∈
      Submodule.span L ((algebraMap A L).mapMatrix '' S) := by
    intro Z
    obtain ⟨s, hs⟩ := hS Z
    have h := h1 _ hs
    have e : (algebraMap A L).mapMatrix (t ^ s • Z) = algebraMap A L t ^ s • (algebraMap A L).mapMatrix Z := by
      ext i j; simp
    rw [e] at h
    exact (Submodule.smul_mem_iff _ (pow_ne_zero s ht)).1 h
  rw [eq_top_iff]
  intro Z _
  rw [Matrix.matrix_eq_sum_single Z]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j (Z i j) = Z i j • (algebraMap A L).mapMatrix (Matrix.single i j (1 : A)) := by
    ext a b
    by_cases h : i = a ∧ j = b <;> simp [Matrix.single_apply, h]
  rw [e]
  exact Submodule.smul_mem _ _ (h2 _)

/- English proof (translation)
Introduce `l _ F n x R _ D f ha hD q hq`. Establish `hn : 1 ≤ n` using `x.a_pos.trans x.a_le`. Establish `ht : algebraMap x.A (FractionRing x.A) x.t ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective x.A (FractionRing x.A))).2 PowerSeries.X_ne_zero`. Establish `hsp` using `span_top (L := FractionRing x.A) x.t ht (mat x.ρ '' (F.G' : Set F.G₀)) fun Z => x.span Z fun i j => ⟨fun _ => Submodule.mem_top, fun h => (h (by simp [ha])).elim⟩`. Take `⟨y, hy, hdet⟩` from `(UpperTheory.V.CA.g_gram _ _ _).1 hsp`.

Establish `hy' : ∀ a, ∃ g, (algebraMap x.A (FractionRing x.A)).mapMatrix (mat x.ρ g) = y a` using `fun a => by`. Take `⟨_, ⟨g, -, rfl⟩, h⟩` from `hy a`. Conclude with `⟨g, h⟩`. Use `choose g hg using hy'`. Use `⟨fun i => g (finProdFinEquiv.symm i), fun i => g (finProdFinEquiv.symm i), fun hm => hdet ?_⟩` and prove the remaining obligations.

Establish `h0` using `congrArg (algebraMap x.A (FractionRing x.A)) (RingHom.mem_ker.1 (hq hm))`. Rewrite `h0` using `[map_zero, ← RingHom.comp_apply, RingHom.map_det]`. Rewrite using `[← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm, ← h0]`. Use `congr 1`. Use extensionality with `a b`.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, tr_of_map hn D f _ hD, Matrix.submatrix_apply, Matrix.of_apply, ← hg, ← hg, ← map_mul, ← map_mul, RingHom.mapMatrix_apply]`. Conclude with `(AddMonoidHom.map_trace (algebraMap x.A (FractionRing x.A)) _).symm`.
-/
theorem UpperTheory.V.Pa.Det.typeIDisc :
    ∀ {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) {R : Type} [CommRing R] (D : GDet n R F.G₀) (f : R →+* x.A), x.a = n → D.map f = GDet.ofRep (mat x.ρ) → ∀ q : Ideal R, q ≤ RingHom.ker f → DiscSt D q := by
  intro l _ F n x R _ D f ha hD q hq
  have hn : 1 ≤ n := x.a_pos.trans x.a_le
  have ht : algebraMap x.A (FractionRing x.A) x.t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective x.A (FractionRing x.A))).2 PowerSeries.X_ne_zero
  have hsp := span_top (L := FractionRing x.A) x.t ht (mat x.ρ '' (F.G' : Set F.G₀)) fun Z =>
    x.span Z fun i j => ⟨fun _ => Submodule.mem_top, fun h => (h (by simp [ha])).elim⟩
  obtain ⟨y, hy, hdet⟩ := (UpperTheory.V.CA.g_gram _ _ _).1 hsp
  have hy' : ∀ a, ∃ g, (algebraMap x.A (FractionRing x.A)).mapMatrix (mat x.ρ g) = y a := fun a => by
    obtain ⟨_, ⟨g, -, rfl⟩, h⟩ := hy a
    exact ⟨g, h⟩
  choose g hg using hy'
  refine ⟨fun i => g (finProdFinEquiv.symm i), fun i => g (finProdFinEquiv.symm i), fun hm => hdet ?_⟩
  have h0 := congrArg (algebraMap x.A (FractionRing x.A)) (RingHom.mem_ker.1 (hq hm))
  rw [map_zero, ← RingHom.comp_apply, RingHom.map_det] at h0
  rw [← Matrix.det_submatrix_equiv_self finProdFinEquiv.symm, ← h0]
  congr 1
  ext a b
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, tr_of_map hn D f _ hD,
    Matrix.submatrix_apply, Matrix.of_apply, ← hg, ← hg, ← map_mul, ← map_mul, RingHom.mapMatrix_apply]
  exact (AddMonoidHom.map_trace (algebraMap x.A (FractionRing x.A)) _).symm
