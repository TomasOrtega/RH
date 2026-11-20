import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemiAlg

noncomputable section

namespace PI.LevelKSplit.W.SemiA

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

section R

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}

/- English proof (translation)
Use extensionality with `a b`. Establish `hcol : ∀ c, Mx.mulVec (Pi.single c (1 : A)) = fun i => Mx i c`. Introduce `c`. Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.mulVec_single]`.

Simplify using the standard rewrite rules. Establish `h1` using `h (Pi.single a 1) (Pi.single b 1)`. Rewrite `h1` using `[hcol, hcol]`. Simplify using `only [Formalism.UG.hform] at h1`. Rewrite using `[show (Formalism.UG.cT σA Mx * JA * Mx) a b = ∑ i, ∑ j, σA (Mx i a) * JA i j * Mx j b by`.

Simplify using `only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm], h1]`. Establish `hs : ∀ i, σA ((Pi.single a (1 : A) : n → A) i) = (Pi.single a (1 : A) : n → A) i`. Introduce `i`. Distinguish the cases in `hi : i = a`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hi]`. Simplify using `only [hs]`. Simplify using `[Pi.single_apply]`.
-/
theorem uj_of_uni {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σA : A →+* A)
    (JA : Matrix n n A) (Mx : Matrix n n A)
    (h : ∀ x y, Formalism.UG.hform σA JA (Matrix.mulVec Mx x) (Matrix.mulVec Mx y) = Formalism.UG.hform σA JA x y) :
    Formalism.UG.cT σA Mx * JA * Mx = JA := by
  classical
  ext a b
  have hcol : ∀ c, Mx.mulVec (Pi.single c (1 : A)) = fun i => Mx i c := by
    intro c
    funext i
    rw [Matrix.mulVec_single]
    simp
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [hcol, hcol] at h1
  simp only [Formalism.UG.hform] at h1
  rw [show (Formalism.UG.cT σA Mx * JA * Mx) a b = ∑ i, ∑ j, σA (Mx i a) * JA i j * Mx j b by
    simp only [Matrix.mul_apply, Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm], h1]
  have hs : ∀ i, σA ((Pi.single a (1 : A) : n → A) i) = (Pi.single a (1 : A) : n → A) i := by
    intro i
    by_cases hi : i = a
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]
  simp only [hs]
  simp [Pi.single_apply]

/- English proof (translation)
Unfold `lin HA.mat`. Conclude with `LinearMap.toMatrix'_toLin' _`.
-/
theorem toMatrix'_lin (g : HA R σ J) :
    LinearMap.toMatrix' (lin R σ J g) =
      ((HA.mat R σ J g : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) := by
  unfold lin HA.mat
  exact LinearMap.toMatrix'_toLin' _

/- English proof (translation)
Establish `hl : lin R σ J g = lin R σ J g'` using `LinearMap.ext h`. Establish `hm` using `congrArg LinearMap.toMatrix' hl`. Rewrite `hm` using `[toMatrix'_lin, toMatrix'_lin]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `hm`.
-/
theorem ext_lin {g g' : HA R σ J} (h : ∀ v, lin R σ J g v = lin R σ J g' v) : g = g' := by
  have hl : lin R σ J g = lin R σ J g' := LinearMap.ext h
  have hm := congrArg LinearMap.toMatrix' hl
  rw [toMatrix'_lin, toMatrix'_lin] at hm
  apply Subtype.ext
  apply Units.ext
  exact hm

def piMat (g : HA R σ J) : Matrix (Fin M) (Fin M) (R ⊗[F] E) :=
  LinearMap.toMatrix' ((datR R σ J P T).Pi (lin R σ J g))

/- English proof (translation)
Unfold `piMat`. Conclude with `LinearMap.toMatrix'_mulVec _ _`.
-/
theorem piMat_mulVec (g : HA R σ J) (v : Fin M → R ⊗[F] E) :
    Matrix.mulVec (piMat (P := P) (T := T) g) v = (datR R σ J P T).Pi (lin R σ J g) v := by
  unfold piMat
  exact LinearMap.toMatrix'_mulVec _ _

/- English proof (translation)
Introduce `g hg`. Take `⟨h1, h2⟩` from `hg`. Establish `hz : ∀ a : Fin r, hR R σ J (ratV (F` using `F) R (P.e a)) (ratV (F := F) R P.z) = 0 := by`. Introduce `a`. Use `hP.2.2.2.1 a` as an intermediate fact.

Unfold `hR ratV hE at *`. Unfold `Formalism.UG.hform sigR JR inclR at *`. Establish `h3` using `congrArg (Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)) this`. Simplify `h3` using `[Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_sum, map_mul]`. Unfold `Ssub uniFlag F0`.

Introduce `b`. Use `Fin.lastCases ?_ (fun b' => ?_) b` and prove the remaining obligations. Establish `key` using `h2 (ratV (F := F) R P.z) hz`. Simplify using `only [Fin.snoc_last]`. Unfold `spanR at key ⊢`.

Use `Submodule.span_mono ?_ key` and prove the remaining obligations. Introduce and unpack `x ⟨a, -, rfl⟩`. Conclude with `⟨Fin.castSucc a, Fin.castSucc_lt_last a, by simp⟩`. Simplify using `only [Fin.snoc_castSucc]`. Unfold `UniC at h1`.

Establish `key` using `h1 b'`. Unfold `spanR at key ⊢`. Use `Submodule.span_mono ?_ key` and prove the remaining obligations. Introduce and unpack `x ⟨a, ha, rfl⟩`. Conclude with `⟨Fin.castSucc a, Fin.castSucc_lt_castSucc_iff.mpr ha, by simp⟩`.
-/
theorem N_le_S' (hP : P.IsStd σ J T) : Nsub R σ J P ≤ Ssub R σ J P := by
  intro g hg
  obtain ⟨h1, h2⟩ := hg
  have hz : ∀ a : Fin r, hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R P.z) = 0 := by
    intro a
    have := hP.2.2.2.1 a
    unfold hR ratV hE at *
    unfold Formalism.UG.hform sigR JR inclR at *
    have h3 := congrArg (Algebra.TensorProduct.includeRight (R := F) (A := R) (B := E)) this
    simpa [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_sum,
      map_mul] using h3
  unfold Ssub uniFlag F0
  intro b
  refine Fin.lastCases ?_ (fun b' => ?_) b
  · have key := h2 (ratV (F := F) R P.z) hz
    simp only [Fin.snoc_last]
    unfold spanR at key ⊢
    refine Submodule.span_mono ?_ key
    rintro x ⟨a, -, rfl⟩
    exact ⟨Fin.castSucc a, Fin.castSucc_lt_last a, by simp⟩
  · simp only [Fin.snoc_castSucc]
    unfold UniC at h1
    have key := h1 b'
    unfold spanR at key ⊢
    refine Submodule.span_mono ?_ key
    rintro x ⟨a, ha, rfl⟩
    exact ⟨Fin.castSucc a, Fin.castSucc_lt_castSucc_iff.mpr ha, by simp⟩

/- English proof (translation)
Introduce `g hg`. Unfold `Hsub stabT tupH at hg`. Rewrite `hg` using `[MulAction.mem_stabilizer_iff]`. Unfold `Ssub uniFlag F0 UniC`. Introduce `b`.

Use `congrFun hg (Fin.castAdd r b)` as an intermediate fact. Unfold `ratTup at this`. Express the relevant statement in the definitionally equal form `lin R σ J g (ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r b))) = ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r b)) at this`. Rewrite `this` using `[Fin.append_left]`. Use `show lin R σ J g (ratV (F := F) R (F0 P b)) - ratV (F := F) R (F0 P b) ∈ _`.

Rewrite using `[this, sub_self]`. Conclude with `Submodule.zero_mem _`.
-/
theorem H_le_S : Hsub R σ J P ≤ Ssub R σ J P := by
  intro g hg
  unfold Hsub stabT tupH at hg
  rw [MulAction.mem_stabilizer_iff] at hg
  unfold Ssub uniFlag F0 UniC
  intro b
  have := congrFun hg (Fin.castAdd r b)
  unfold ratTup at this
  change lin R σ J g (ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r b))) =
    ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r b)) at this
  rw [Fin.append_left] at this
  show lin R σ J g (ratV (F := F) R (F0 P b)) - ratV (F := F) R (F0 P b) ∈ _
  rw [this, sub_self]
  exact Submodule.zero_mem _

/- English proof (translation)
Establish `hfix : ∀ b, lin R σ J h (ratV (F` using `F) R (P.e b)) = ratV (F := F) R (P.e b) := by`. Introduce `b`. Establish `hh'` using `hh`. Unfold `Hsub stabT tupH at hh'`. Rewrite `hh'` using `[MulAction.mem_stabilizer_iff]`.

Use `congrFun hh' (Fin.castAdd r (Fin.castSucc b))` as an intermediate fact. Unfold `ratTup at this`. Express the relevant statement in the definitionally equal form `lin R σ J h (ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r (Fin.castSucc b)))) = ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r (Fin.castSucc b))) at this`. Rewrite `this` using `[Fin.append_left]`. Simplify `this` using `[F0, Fin.snoc_castSucc]`.

Establish `huni : h ∈ uniFlag R σ J P.e` using `by show UniC R σ J P.e h`. Introduce `b`. Rewrite using `[hfix b, sub_self]`. Conclude with `Submodule.zero_mem _`. Take `⟨hn1, hn2⟩` from `hn`.

Use `⟨?_, fun v hv => ?_⟩` and prove the remaining obligations. Conclude with `(uniFlag R σ J P.e).mul_mem ((uniFlag R σ J P.e).mul_mem huni hn1) ((uniFlag R σ J P.e).inv_mem huni)`. Establish `hu : InXperp R σ J P (lin R σ J h⁻¹ v)`. Introduce `a`. Rewrite using `[← hR_lin h, lin_lin_inv, hfix a]`.

Conclude with `hv a`. Establish `h1` using `hn2 _ hu`. Establish `h2 : lin R σ J h (lin R σ J n (lin R σ J h⁻¹ v) - lin R σ J h⁻¹ v) ∈ spanR (F` using `F) R P.e Set.univ := uni_map_le huni Set.univ (fun _ _ _ _ => Set.mem_univ _) (Submodule.mem_map_of_mem h1)`. Rewrite `h2` using `[map_sub, lin_lin_inv]`. Rewrite using `[lin_mul, lin_mul]`.

Simplify using `using h2`.
-/
theorem norm_N {h n : HA R σ J} (hh : h ∈ Hsub R σ J P) (hn : n ∈ Nsub R σ J P) :
    h * n * h⁻¹ ∈ Nsub R σ J P := by
  have hfix : ∀ b, lin R σ J h (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := by
    intro b
    have hh' := hh
    unfold Hsub stabT tupH at hh'
    rw [MulAction.mem_stabilizer_iff] at hh'
    have := congrFun hh' (Fin.castAdd r (Fin.castSucc b))
    unfold ratTup at this
    change lin R σ J h (ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r (Fin.castSucc b)))) =
      ratV (F := F) R (Fin.append (F0 P) P.f (Fin.castAdd r (Fin.castSucc b))) at this
    rw [Fin.append_left] at this
    simpa [F0, Fin.snoc_castSucc] using this
  have huni : h ∈ uniFlag R σ J P.e := by
    show UniC R σ J P.e h
    intro b
    rw [hfix b, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨hn1, hn2⟩ := hn
  refine ⟨?_, fun v hv => ?_⟩
  · exact (uniFlag R σ J P.e).mul_mem ((uniFlag R σ J P.e).mul_mem huni hn1)
      ((uniFlag R σ J P.e).inv_mem huni)
  · have hu : InXperp R σ J P (lin R σ J h⁻¹ v) := by
      intro a
      rw [← hR_lin h, lin_lin_inv, hfix a]
      exact hv a
    have h1 := hn2 _ hu
    have h2 : lin R σ J h (lin R σ J n (lin R σ J h⁻¹ v) - lin R σ J h⁻¹ v) ∈
        spanR (F := F) R P.e Set.univ :=
      uni_map_le huni Set.univ (fun _ _ _ _ => Set.mem_univ _) (Submodule.mem_map_of_mem h1)
    rw [map_sub, lin_lin_inv] at h2
    rw [lin_mul, lin_mul]
    simpa using h2

variable (hσσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (hP : P.IsStd σ J T)
include hσσ hJ hP

/- English proof (translation)
Unfold `spanR`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `x ⟨b, hb, rfl⟩`. Use `Submodule.subset_span ?_` and prove the remaining obligations. Proceed by induction on `b using Fin.lastCases with`.

Consider the case `last => exact absurd hb hs`. Consider the case `cast b' => exact ⟨b', by simp [F0, datR]⟩`.
-/
private theorem spanR_of_last_not_mem (s : Set (Fin (r + 1))) (hs : Fin.last r ∉ s) :
    spanR (F := F) R (F0 P) s ≤ Submodule.span (R ⊗[F] E) (Set.range (datR R σ J P T).e) := by
  unfold spanR
  refine Submodule.span_le.mpr ?_
  rintro x ⟨b, hb, rfl⟩
  refine Submodule.subset_span ?_
  induction b using Fin.lastCases with
  | last => exact absurd hb hs
  | cast b' => exact ⟨b', by simp [F0, datR]⟩

/- English proof (translation)
Introduce `a`. Establish `key` using `(show UniC R σ J (F0 P) g from hg) (Fin.castSucc a)`. Establish `hle` using `spanR_of_last_not_mem (R := R) (σ := σ) (J := J) (P := P) (T := T) hσσ hJ hP {b | b < Fin.castSucc a} (fun h => lt_asymm h (Fin.castSucc_lt_last a))`. Establish `h2` using `Submodule.add_mem _ (hle key) (Submodule.subset_span (⟨a, rfl⟩ : (datR R σ J P T).e a ∈ Set.range (datR R σ J P T).e))`. Establish `hF : ratV (F` using `F) R (F0 P (Fin.castSucc a)) = (datR R σ J P T).e a := by`.

Simplify using `[F0, datR]`. Rewrite `h2` using `[hF, sub_add_cancel]`. Conclude with `h2`.
-/
private theorem mapX_lin_of_mem_Ssub {g : HA R σ J} (hg : g ∈ Ssub R σ J P) :
    (datR R σ J P T).MapX (lin R σ J g) := by
  intro a
  have key := (show UniC R σ J (F0 P) g from hg) (Fin.castSucc a)
  have hle := spanR_of_last_not_mem (R := R) (σ := σ) (J := J) (P := P) (T := T) hσσ hJ hP {b | b < Fin.castSucc a}
    (fun h => lt_asymm h (Fin.castSucc_lt_last a))
  have h2 := Submodule.add_mem _ (hle key)
    (Submodule.subset_span (⟨a, rfl⟩ : (datR R σ J P T).e a ∈ Set.range (datR R σ J P T).e))
  have hF : ratV (F := F) R (F0 P (Fin.castSucc a)) = (datR R σ J P T).e a := by
    simp [F0, datR]
  rw [hF, sub_add_cancel] at h2
  exact h2

/- English proof (translation)
Establish `hgi : g⁻¹ ∈ Ssub R σ J P` using `(Ssub R σ J P).inv_mem hg`. Use `SemiG.Dat.mapW_of_inv (D := datR R σ J P T) (Si := lin R σ J g⁻¹) (fun v => by rw [lin_lin_inv]) (fun x y => by show hR R σ J (lin R σ J g x) (lin R σ J g y) = hR R σ J x y` and prove the remaining obligations. Rewrite using `[hR_lin]) (mapX_lin_of_mem_Ssub hσσ hJ hP hgi) ?_`. Establish `key` using `(show UniC R σ J (F0 P) g⁻¹ from hgi) (Fin.last r)`. Establish `hle` using `spanR_of_last_not_mem (R := R) (σ := σ) (J := J) (P := P) (T := T) hσσ hJ hP {b | b < Fin.last r} (fun h => lt_irrefl (Fin.last r) h)`.

Establish `hF : ratV (F` using `F) R (F0 P (Fin.last r)) = (datR R σ J P T).z := by`. Simplify using `[F0, datR]`. Rewrite `key` using `[hF]`. Conclude with `hle key`.
-/
private theorem mapW_lin_of_mem_Ssub {g : HA R σ J} (hg : g ∈ Ssub R σ J P) :
    (datR R σ J P T).MapW (lin R σ J g) := by
  have hgi : g⁻¹ ∈ Ssub R σ J P := (Ssub R σ J P).inv_mem hg
  refine SemiG.Dat.mapW_of_inv (D := datR R σ J P T) (Si := lin R σ J g⁻¹)
    (fun v => by rw [lin_lin_inv]) (fun x y => by
      show hR R σ J (lin R σ J g x) (lin R σ J g y) = hR R σ J x y
      rw [hR_lin]) (mapX_lin_of_mem_Ssub hσσ hJ hP hgi) ?_
  have key := (show UniC R σ J (F0 P) g⁻¹ from hgi) (Fin.last r)
  have hle := spanR_of_last_not_mem (R := R) (σ := σ) (J := J) (P := P) (T := T) hσσ hJ hP {b | b < Fin.last r}
    (fun h => lt_irrefl (Fin.last r) h)
  have hF : ratV (F := F) R (F0 P (Fin.last r)) = (datR R σ J P T).z := by
    simp [F0, datR]
  rw [hF] at key
  exact hle key

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Rewrite using `[LinearMap.comp_apply, SemiG.Dat.Pi_comp (D := datR R σ J P T) (datR_hyp hσσ hJ hP) (mapX_lin_of_mem_Ssub hσσ hJ hP hg) (mapW_lin_of_mem_Ssub hσσ hJ hP hg')]`. Establish `hl : lin R σ J (g * g') = lin R σ J g ∘ₗ lin R σ J g'` using `LinearMap.ext fun x => by rw [lin_mul]; rfl`. Rewrite using `[hl]`.
-/
theorem Pi_lin_mul {g g' : HA R σ J} (hg : g ∈ Ssub R σ J P) (hg' : g' ∈ Ssub R σ J P) :
    (datR R σ J P T).Pi (lin R σ J (g * g')) =
      (datR R σ J P T).Pi (lin R σ J g) ∘ₗ (datR R σ J P T).Pi (lin R σ J g') := by
  apply LinearMap.ext
  intro v
  rw [LinearMap.comp_apply, SemiG.Dat.Pi_comp (D := datR R σ J P T) (datR_hyp hσσ hJ hP)
    (mapX_lin_of_mem_Ssub hσσ hJ hP hg) (mapW_lin_of_mem_Ssub hσσ hJ hP hg')]
  have hl : lin R σ J (g * g') = lin R σ J g ∘ₗ lin R σ J g' :=
    LinearMap.ext fun x => by rw [lin_mul]; rfl
  rw [hl]

/- English proof (translation)
Establish `hsym : ∀ x y : Fin M → E, hE σ J y x = σ (hE σ J x y)`. Introduce `x y`. Unfold `hE Formalism.UG.hform`. Simplify using `only [map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσσ, hJ.1]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hRrat : ∀ x y : Fin M → E, (datR R σ J P T).hL (ratV (F` using `F) R x) (ratV (F := F) R y) = inclR (F := F) R (hE σ J x y) := by`. Introduce `x y`. Use `show (datR R σ J P T).h (ratV (F := F) R x) (ratV (F := F) R y) = _`.

Unfold `SemiG.Dat.h datR ratV hE Formalism.UG.hform sigR JR inclR`. Simplify using `[Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_sum, map_mul]`. Establish `hee : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).e b) ((datR R σ J P T).e a) = 0`. Introduce `b a`. Use `show (datR R σ J P T).hL (ratV (F := F) R (P.e b)) (ratV (F := F) R (P.e a)) = 0`.

Rewrite using `[hRrat, hP.1 b a, map_zero]`. Establish `hff : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).f b) ((datR R σ J P T).f a) = 0`. Introduce `b a`. Use `show (datR R σ J P T).hL (ratV (F := F) R (P.f b)) (ratV (F := F) R (P.f a)) = 0`. Rewrite using `[hRrat, hP.2.1 b a, map_zero]`.

Establish `hef : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).e b) ((datR R σ J P T).f a) = if b = a then 1 else 0`. Introduce `b a`. Use `show (datR R σ J P T).hL (ratV (F := F) R (P.e b)) (ratV (F := F) R (P.f a)) = _`. Rewrite using `[hRrat, hP.2.2.1 b a]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hfe : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).f b) ((datR R σ J P T).e a) = if b = a then 1 else 0`. Introduce `b a`. Use `show (datR R σ J P T).hL (ratV (F := F) R (P.f b)) (ratV (F := F) R (P.e a)) = _`. Rewrite using `[hRrat, hsym, hP.2.2.1 a b]`. Distinguish the cases in `h : b = a`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm h), if_neg h]`. Simplify using the standard rewrite rules. Establish `hez : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).e b) (datR R σ J P T).z = 0`.

Introduce `b`. Use `show (datR R σ J P T).hL (ratV (F := F) R (P.e b)) (ratV (F := F) R P.z) = 0`. Rewrite using `[hRrat, hP.2.2.2.1 b, map_zero]`. Establish `hfz : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).f b) (datR R σ J P T).z = 0`. Introduce `b`.

Use `show (datR R σ J P T).hL (ratV (F := F) R (P.f b)) (ratV (F := F) R P.z) = 0`. Rewrite using `[hRrat, hP.2.2.2.2.1 b, map_zero]`. Establish `hze : ∀ a, (datR R σ J P T).hL (datR R σ J P T).z ((datR R σ J P T).e a) = 0`. Introduce `a`. Use `show (datR R σ J P T).hL (ratV (F := F) R P.z) (ratV (F := F) R (P.e a)) = 0`.

Rewrite using `[hRrat, hsym, hP.2.2.2.1 a, map_zero, map_zero]`. Establish `hzf : ∀ a, (datR R σ J P T).hL (datR R σ J P T).z ((datR R σ J P T).f a) = 0`. Introduce `a`. Use `show (datR R σ J P T).hL (ratV (F := F) R P.z) (ratV (F := F) R (P.f a)) = 0`. Rewrite using `[hRrat, hsym, hP.2.2.2.2.1 a, map_zero, map_zero]`.

Establish `hzz : (datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z (datR R σ J P T).z = 1` using `by show inclR (F := F) R ((algebraMap F E (-T))⁻¹) * (datR R σ J P T).hL (ratV (F := F) R P.z) (ratV (F := F) R P.z) = 1`. Rewrite using `[hRrat, hP.2.2.2.2.2.1, ← map_mul, inv_mul_cancel₀, map_one]`. Conclude with `(map_ne_zero _).mpr (neg_ne_zero.mpr hP.2.2.2.2.2.2)`. Establish `hpU : ∀ u, (datR R σ J P T).pU u = ∑ a, (datR R σ J P T).hL ((datR R σ J P T).f a) u • (datR R σ J P T).e a + ∑ a, (datR R σ J P T).hL ((datR R σ J P T).e a) u • (datR R σ J P T).f a + ((datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z u) • (datR R σ J P T).z`. Introduce `u`.

Simplify using `only [SemiG.Dat.pU, SemiG.Dat.pX, SemiG.Dat.pXv, SemiG.Dat.pz, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]`. Establish `key : ∀ v, (datR R σ J P T).pU ((datR R σ J P T).pU v) = (datR R σ J P T).pU v`. Introduce `v`. Establish `c1 : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).f b) ((datR R σ J P T).pU v) = (datR R σ J P T).hL ((datR R σ J P T).f b) v`. Introduce `b`.

Rewrite using `[hpU v]`. Simplify using `only [map_add, map_sum, map_smul, smul_eq_mul, hfe b, hff b, hfz b]`. Simplify using the standard rewrite rules. Establish `c2 : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).e b) ((datR R σ J P T).pU v) = (datR R σ J P T).hL ((datR R σ J P T).e b) v`. Introduce `b`.

Rewrite using `[hpU v]`. Simplify using `only [map_add, map_sum, map_smul, smul_eq_mul, hee b, hef b, hez b]`. Simplify using the standard rewrite rules. Establish `c3 : (datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z ((datR R σ J P T).pU v) = (datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z v`. Rewrite using `[hpU v]`.

Simplify using `only [map_add, map_sum, map_smul, smul_eq_mul, hze, hzf, mul_zero, Finset.sum_const_zero, zero_add]`. Take the linear combination `((datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z v) * hzz`. Rewrite using `[hpU ((datR R σ J P T).pU v), c3]`. Simplify using `only [c1, c2]`. Conclude with `(hpU v).symm`.

Establish `hid : lin R σ J 1 = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Unfold `lin`. Use `show (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVecLin v = v`.

Rewrite using `[Matrix.mulVecLin_apply, Matrix.one_mulVec]`. Unfold `SemiG.Dat.Pi`. Rewrite using `[hid, LinearMap.id_comp]`. Unfold `SemiG.Dat.pW`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `v`. Simplify using `only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub, key]`. Normalize the expressions using the abelian group laws.
-/
theorem Pi_lin_one : (datR R σ J P T).Pi (lin R σ J 1) = LinearMap.id := by
  classical
  have hsym : ∀ x y : Fin M → E, hE σ J y x = σ (hE σ J x y) := by
    intro x y
    unfold hE Formalism.UG.hform
    simp only [map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσσ, hJ.1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hRrat : ∀ x y : Fin M → E, (datR R σ J P T).hL (ratV (F := F) R x) (ratV (F := F) R y) =
      inclR (F := F) R (hE σ J x y) := by
    intro x y
    show (datR R σ J P T).h (ratV (F := F) R x) (ratV (F := F) R y) = _
    unfold SemiG.Dat.h datR ratV hE Formalism.UG.hform sigR JR inclR
    simp [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul, map_sum,
      map_mul]
  have hee : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).e b) ((datR R σ J P T).e a) = 0 := by
    intro b a
    show (datR R σ J P T).hL (ratV (F := F) R (P.e b)) (ratV (F := F) R (P.e a)) = 0
    rw [hRrat, hP.1 b a, map_zero]
  have hff : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).f b) ((datR R σ J P T).f a) = 0 := by
    intro b a
    show (datR R σ J P T).hL (ratV (F := F) R (P.f b)) (ratV (F := F) R (P.f a)) = 0
    rw [hRrat, hP.2.1 b a, map_zero]
  have hef : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).e b) ((datR R σ J P T).f a) = if b = a then 1 else 0 := by
    intro b a
    show (datR R σ J P T).hL (ratV (F := F) R (P.e b)) (ratV (F := F) R (P.f a)) = _
    rw [hRrat, hP.2.2.1 b a]
    split_ifs <;> simp
  have hfe : ∀ b a, (datR R σ J P T).hL ((datR R σ J P T).f b) ((datR R σ J P T).e a) = if b = a then 1 else 0 := by
    intro b a
    show (datR R σ J P T).hL (ratV (F := F) R (P.f b)) (ratV (F := F) R (P.e a)) = _
    rw [hRrat, hsym, hP.2.2.1 a b]
    by_cases h : b = a
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
      simp
  have hez : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).e b) (datR R σ J P T).z = 0 := by
    intro b
    show (datR R σ J P T).hL (ratV (F := F) R (P.e b)) (ratV (F := F) R P.z) = 0
    rw [hRrat, hP.2.2.2.1 b, map_zero]
  have hfz : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).f b) (datR R σ J P T).z = 0 := by
    intro b
    show (datR R σ J P T).hL (ratV (F := F) R (P.f b)) (ratV (F := F) R P.z) = 0
    rw [hRrat, hP.2.2.2.2.1 b, map_zero]
  have hze : ∀ a, (datR R σ J P T).hL (datR R σ J P T).z ((datR R σ J P T).e a) = 0 := by
    intro a
    show (datR R σ J P T).hL (ratV (F := F) R P.z) (ratV (F := F) R (P.e a)) = 0
    rw [hRrat, hsym, hP.2.2.2.1 a, map_zero, map_zero]
  have hzf : ∀ a, (datR R σ J P T).hL (datR R σ J P T).z ((datR R σ J P T).f a) = 0 := by
    intro a
    show (datR R σ J P T).hL (ratV (F := F) R P.z) (ratV (F := F) R (P.f a)) = 0
    rw [hRrat, hsym, hP.2.2.2.2.1 a, map_zero, map_zero]
  have hzz : (datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z (datR R σ J P T).z = 1 := by
    show inclR (F := F) R ((algebraMap F E (-T))⁻¹) *
      (datR R σ J P T).hL (ratV (F := F) R P.z) (ratV (F := F) R P.z) = 1
    rw [hRrat, hP.2.2.2.2.2.1, ← map_mul, inv_mul_cancel₀, map_one]
    exact (map_ne_zero _).mpr (neg_ne_zero.mpr hP.2.2.2.2.2.2)
  have hpU : ∀ u, (datR R σ J P T).pU u = ∑ a, (datR R σ J P T).hL ((datR R σ J P T).f a) u • (datR R σ J P T).e a + ∑ a, (datR R σ J P T).hL ((datR R σ J P T).e a) u • (datR R σ J P T).f a +
      ((datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z u) • (datR R σ J P T).z := by
    intro u
    simp only [SemiG.Dat.pU, SemiG.Dat.pX, SemiG.Dat.pXv, SemiG.Dat.pz, LinearMap.add_apply,
      LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.smul_apply,
      smul_eq_mul]
  have key : ∀ v, (datR R σ J P T).pU ((datR R σ J P T).pU v) = (datR R σ J P T).pU v := by
    intro v
    have c1 : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).f b) ((datR R σ J P T).pU v) = (datR R σ J P T).hL ((datR R σ J P T).f b) v := by
      intro b
      rw [hpU v]
      simp only [map_add, map_sum, map_smul, smul_eq_mul, hfe b, hff b, hfz b]
      simp
    have c2 : ∀ b, (datR R σ J P T).hL ((datR R σ J P T).e b) ((datR R σ J P T).pU v) = (datR R σ J P T).hL ((datR R σ J P T).e b) v := by
      intro b
      rw [hpU v]
      simp only [map_add, map_sum, map_smul, smul_eq_mul, hee b, hef b, hez b]
      simp
    have c3 : (datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z ((datR R σ J P T).pU v) = (datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z v := by
      rw [hpU v]
      simp only [map_add, map_sum, map_smul, smul_eq_mul, hze, hzf, mul_zero,
        Finset.sum_const_zero, zero_add]
      linear_combination ((datR R σ J P T).tz * (datR R σ J P T).hL (datR R σ J P T).z v) * hzz
    rw [hpU ((datR R σ J P T).pU v), c3]
    simp only [c1, c2]
    exact (hpU v).symm
  have hid : lin R σ J 1 = LinearMap.id := by
    apply LinearMap.ext
    intro v
    unfold lin
    show (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVecLin v = v
    rw [Matrix.mulVecLin_apply, Matrix.one_mulVec]
  unfold SemiG.Dat.Pi
  rw [hid, LinearMap.id_comp]
  unfold SemiG.Dat.pW
  apply LinearMap.ext
  intro v
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply,
    map_sub, key]
  abel

def piU (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : GL (Fin M) (R ⊗[F] E) where
  val := piMat (P := P) (T := T) g
  inv := piMat (P := P) (T := T) g⁻¹
  val_inv := by
    rw [piMat, piMat, ← LinearMap.toMatrix'_comp,
      ← Pi_lin_mul hσσ hJ hP hg ((Ssub R σ J P).inv_mem hg), mul_inv_cancel,
      Pi_lin_one hσσ hJ hP, LinearMap.toMatrix'_id]
  inv_val := by
    rw [piMat, piMat, ← LinearMap.toMatrix'_comp,
      ← Pi_lin_mul hσσ hJ hP ((Ssub R σ J P).inv_mem hg) hg, inv_mul_cancel,
      Pi_lin_one hσσ hJ hP, LinearMap.toMatrix'_id]

/- English proof (translation)
Introduce `x y`. Use `show hR R σ J (lin R σ J g x) (lin R σ J g y) = hR R σ J x y`. Rewrite using `[hR_lin]`.
-/
private theorem uni_lin' (g : HA R σ J) : (datR R σ J P T).Uni (lin R σ J g) := by
  intro x y
  show hR R σ J (lin R σ J g x) (lin R σ J g y) = hR R σ J x y
  rw [hR_lin]

/- English proof (translation)
Establish `hU` using `SemiG.Dat.Pi_uni (D := datR R σ J P T) (datR_hyp hσσ hJ hP) (mapW_lin_of_mem_Ssub hσσ hJ hP hg) (uni_lin' hσσ hJ hP g)`. Establish `hm` using `uj_of_uni (sigR R σ) (JR R J) (piMat (P := P) (T := T) g) (fun x y => by`. Rewrite using `[piMat_mulVec, piMat_mulVec]`. Conclude with `hU x y)`. Conclude with `hm`.
-/
theorem piU_mem (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : piU hσσ hJ hP g hg ∈ HR R σ J := by
  have hU := SemiG.Dat.Pi_uni (D := datR R σ J P T) (datR_hyp hσσ hJ hP)
    (mapW_lin_of_mem_Ssub hσσ hJ hP hg) (uni_lin' hσσ hJ hP g)
  have hm := uj_of_uni (sigR R σ) (JR R J) (piMat (P := P) (T := T) g) (fun x y => by
    rw [piMat_mulVec, piMat_mulVec]
    exact hU x y)
  exact hm

def piG (g : HA R σ J) (hg : g ∈ Ssub R σ J P) : HA R σ J :=
  ⟨piU hσσ hJ hP g hg, piU_mem hσσ hJ hP g hg⟩

/- English proof (translation)
Unfold `lin`. Conclude with `Matrix.toLin'_toMatrix' _`.
-/
theorem lin_piG (g : HA R σ J) (hg : g ∈ Ssub R σ J P) :
    lin R σ J (piG hσσ hJ hP g hg) = (datR R σ J P T).Pi (lin R σ J g) := by
  unfold lin
  exact Matrix.toLin'_toMatrix' _

end R

end PI.LevelKSplit.W.SemiA
