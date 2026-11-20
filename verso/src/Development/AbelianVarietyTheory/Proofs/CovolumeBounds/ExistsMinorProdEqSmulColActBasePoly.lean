import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsWeightedHomogeneousOfMemOrbitSpan

open MvPolynomial Matrix Module

namespace GlobalTheory.Harm

section LinearAlgebra

variable {K V V' W ι : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V']
  [Module K V'] [AddCommGroup W] [Module K W]

/- English proof (translation)
Set `e₀ : V ≃ₗ[K] V'` to `LinearEquiv.ofFinrankEq V V' hd`. Establish `hw' : LinearIndependent K (e₀.symm ∘ w)` using `hw.map' e₀.symm.toLinearMap e₀.symm.ker`. Take `⟨g, hg⟩` from `Submodule.exists_linearEquiv_restrict_eq ((Basis.span hv).equiv (Basis.span hw') (Equiv.refl ι))`. Use `⟨g.trans e₀, fun i => ?_⟩` and prove the remaining obligations. Use `hg (Basis.span hv i)` as an intermediate fact.

Rewrite `this` using `[Basis.equiv_apply, Basis.span_apply, Basis.span_apply]`. Simplify using `[← this]`.
-/
theorem exists_linearEquiv_apply_eq [FiniteDimensional K V] [FiniteDimensional K V']
    (hd : finrank K V = finrank K V') {v : ι → V} {w : ι → V'} (hv : LinearIndependent K v)
    (hw : LinearIndependent K w) : ∃ e : V ≃ₗ[K] V', ∀ i, e (v i) = w i := by
  let e₀ : V ≃ₗ[K] V' := LinearEquiv.ofFinrankEq V V' hd
  have hw' : LinearIndependent K (e₀.symm ∘ w) := hw.map' e₀.symm.toLinearMap e₀.symm.ker
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((Basis.span hv).equiv (Basis.span hw') (Equiv.refl ι))
  refine ⟨g.trans e₀, fun i => ?_⟩
  have := hg (Basis.span hv i)
  rw [Basis.equiv_apply, Basis.span_apply, Basis.span_apply] at this
  simp [← this]

/- English proof (translation)
Take `⟨s, hs⟩` from `E.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hE)`. Take `⟨s', hs'⟩` from `E'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hE')`. Establish `hs1 (y) : E (s y) = y` using `LinearMap.congr_fun hs y`. Establish `hs1' (y) : E' (s' y) = y` using `LinearMap.congr_fun hs' y`. Establish `hd : finrank K (LinearMap.ker E) = finrank K (LinearMap.ker E')`.

Establish `h1` using `E.finrank_range_add_finrank_ker`. Establish `h2` using `E'.finrank_range_add_finrank_ker`. Rewrite `h1` using `[LinearMap.range_eq_top.mpr hE]`. Rewrite `h2` using `[LinearMap.range_eq_top.mpr hE']`. Use linear arithmetic over natural numbers and integers.

Take `⟨e, he⟩` from `exists_linearEquiv_apply_eq hd (v := fun i => ⟨v i, h i⟩) (w := fun i => ⟨v' i, h' i⟩) (LinearIndependent.of_comp (LinearMap.ker E).subtype hv) (LinearIndependent.of_comp (LinearMap.ker E').subtype hv')`. Set `π : V →ₗ[K] LinearMap.ker E` to `LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ E) fun x => by simp [hs1]`. Establish `hπ (x) : (π x : V) = x - s (E x)` using `rfl`. Set `f : V →ₗ[K] V` to `s' ∘ₗ E + (LinearMap.ker E').subtype ∘ₗ e.toLinearMap ∘ₗ π`. Establish `hf (x) : f x = s' (E x) + e (π x)` using `rfl`.

Establish `hEf (x) : E' (f x) = E x`. Rewrite using `[hf, map_add, hs1', LinearMap.mem_ker.mp (e (π x)).2, add_zero]`. Establish `hinj : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Establish `h0 : E x = 0` using `by rw [← hEf, hx, map_zero]`. Rewrite `hx` using `[hf, h0, map_zero, zero_add, ZeroMemClass.coe_eq_zero, map_eq_zero_iff _ e.injective]`. Simplify `(hπ x).symm` using `[h0, hx]`. Use `⟨LinearEquiv.ofInjectiveEndo f hinj, hEf, fun i => ?_⟩` and prove the remaining obligations. Establish `: π (v i) = ⟨v i, h i⟩` using `Subtype.ext (by simp [hπ, h i])`.

Express the relevant statement in the definitionally equal form `f (v i) = _`. Rewrite using `[hf, h i, map_zero, zero_add, this, he]`.
-/
theorem exists_linearEquiv_comp_eq_and_apply_eq [FiniteDimensional K V] {E E' : V →ₗ[K] W}
    (hE : Function.Surjective E) (hE' : Function.Surjective E') {v v' : ι → V}
    (hv : LinearIndependent K v) (hv' : LinearIndependent K v') (h : ∀ i, E (v i) = 0)
    (h' : ∀ i, E' (v' i) = 0) :
    ∃ g : V ≃ₗ[K] V, (∀ x, E' (g x) = E x) ∧ ∀ i, g (v i) = v' i := by
  obtain ⟨s, hs⟩ := E.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hE)
  obtain ⟨s', hs'⟩ := E'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hE')
  have hs1 (y) : E (s y) = y := LinearMap.congr_fun hs y
  have hs1' (y) : E' (s' y) = y := LinearMap.congr_fun hs' y
  have hd : finrank K (LinearMap.ker E) = finrank K (LinearMap.ker E') := by
    have h1 := E.finrank_range_add_finrank_ker
    have h2 := E'.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hE] at h1
    rw [LinearMap.range_eq_top.mpr hE'] at h2
    omega
  obtain ⟨e, he⟩ := exists_linearEquiv_apply_eq hd (v := fun i => ⟨v i, h i⟩)
    (w := fun i => ⟨v' i, h' i⟩) (LinearIndependent.of_comp (LinearMap.ker E).subtype hv)
    (LinearIndependent.of_comp (LinearMap.ker E').subtype hv')
  let π : V →ₗ[K] LinearMap.ker E :=
    LinearMap.codRestrict _ (LinearMap.id - s ∘ₗ E) fun x => by simp [hs1]
  have hπ (x) : (π x : V) = x - s (E x) := rfl
  let f : V →ₗ[K] V := s' ∘ₗ E + (LinearMap.ker E').subtype ∘ₗ e.toLinearMap ∘ₗ π
  have hf (x) : f x = s' (E x) + e (π x) := rfl
  have hEf (x) : E' (f x) = E x := by
    rw [hf, map_add, hs1', LinearMap.mem_ker.mp (e (π x)).2, add_zero]
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : E x = 0 := by rw [← hEf, hx, map_zero]
    rw [hf, h0, map_zero, zero_add, ZeroMemClass.coe_eq_zero, map_eq_zero_iff _ e.injective] at hx
    simpa [h0, hx] using (hπ x).symm
  refine ⟨LinearEquiv.ofInjectiveEndo f hinj, hEf, fun i => ?_⟩
  have : π (v i) = ⟨v i, h i⟩ := Subtype.ext (by simp [hπ, h i])
  change f (v i) = _
  rw [hf, h i, map_zero, zero_add, this, he]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨v, linearIndependent_empty_type, fun b => b.elim0⟩`. Consider the case `succ m ih`. Take `⟨w, hw, hvw⟩` from `ih (by omega) (Fin.init v)`. Establish `key : ∃ x, LinearIndependent K (Fin.snoc w x : Fin (m + 1) → V) ∧ v (Fin.last m) ∈ Submodule.span K (Set.range (Fin.snoc w x : Fin (m + 1) → V))`.

Distinguish the cases in `hx : v (Fin.last m) ∈ Submodule.span K (Set.range w)`. Take `⟨x, hx'⟩` from `exists_linearIndependent_snoc_of_lt_finrank hw (by omega)`. Use `⟨x, hx', Submodule.span_mono ?_ hx⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `⟨a.castSucc, by simp⟩`.

Conclude with `⟨_, hw.finSnoc hx, Submodule.subset_span ⟨Fin.last m, by simp⟩⟩`. Take `⟨x, hx, hvx⟩` from `key`. Use `⟨_, hx, fun b => ?_⟩` and prove the remaining obligations. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => simpa [← Fin.top_eq_last] using hvx`.

Consider the case `cast b`. Use `Submodule.span_mono ?_ (hvw b)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `⟨a.castSucc, by simpa using ha, by simp⟩`.
-/
theorem exists_linearIndependent_flag {m : ℕ} (hm : m ≤ finrank K V) (v : Fin m → V) :
    ∃ w : Fin m → V, LinearIndependent K w ∧
      ∀ b, v b ∈ Submodule.span K (w '' Set.Iic b) := by
  induction m with
  | zero => exact ⟨v, linearIndependent_empty_type, fun b => b.elim0⟩
  | succ m ih =>
    obtain ⟨w, hw, hvw⟩ := ih (by omega) (Fin.init v)
    have key : ∃ x, LinearIndependent K (Fin.snoc w x : Fin (m + 1) → V) ∧
        v (Fin.last m) ∈ Submodule.span K (Set.range (Fin.snoc w x : Fin (m + 1) → V)) := by
      by_cases hx : v (Fin.last m) ∈ Submodule.span K (Set.range w)
      · obtain ⟨x, hx'⟩ := exists_linearIndependent_snoc_of_lt_finrank hw (by omega)
        refine ⟨x, hx', Submodule.span_mono ?_ hx⟩
        rintro _ ⟨a, rfl⟩
        exact ⟨a.castSucc, by simp⟩
      · exact ⟨_, hw.finSnoc hx, Submodule.subset_span ⟨Fin.last m, by simp⟩⟩
    obtain ⟨x, hx, hvx⟩ := key
    refine ⟨_, hx, fun b => ?_⟩
    induction b using Fin.lastCases with
    | last => simpa [← Fin.top_eq_last] using hvx
    | cast b =>
      refine Submodule.span_mono ?_ (hvw b)
      rintro _ ⟨a, ha, rfl⟩
      exact ⟨a.castSucc, by simpa using ha, by simp⟩

/- English proof (translation)
Take `⟨w, hw, hvw⟩` from `exists_linearIndependent_flag hm (fun b => (⟨v b, hv b⟩ : U))`. Use `⟨U.subtype ∘ w, hw.map' _ U.ker_subtype, fun a => (w a).2, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[Set.image_comp, Submodule.span_image]`. Conclude with `⟨_, hvw b, rfl⟩`.
-/
theorem exists_linearIndependent_flag_mem {m : ℕ} (U : Submodule K V) (hm : m ≤ finrank K U)
    (v : Fin m → V) (hv : ∀ b, v b ∈ U) :
    ∃ w : Fin m → V, LinearIndependent K w ∧ (∀ a, w a ∈ U) ∧
      ∀ b, v b ∈ Submodule.span K (w '' Set.Iic b) := by
  obtain ⟨w, hw, hvw⟩ := exists_linearIndependent_flag hm (fun b => (⟨v b, hv b⟩ : U))
  refine ⟨U.subtype ∘ w, hw.map' _ U.ker_subtype, fun a => (w a).2, fun b => ?_⟩
  rw [Set.image_comp, Submodule.span_image]
  exact ⟨_, hvw b, rfl⟩

end LinearAlgebra

section Transitive

variable {K : Type*} [Field K] {κ ι ι' : Type*} [Fintype κ]

/- English proof (translation)
Establish `h1` using `(Matrix.of ε).mulVecLin.finrank_range_add_finrank_ker`. Establish `h2` using `(LinearMap.range (Matrix.of ε).mulVecLin).finrank_le`. Rewrite `h1`, `h2` using `[finrank_fintype_fun_eq_card]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_le_card_add_finrank_ker [Fintype ι] (ε : ι → κ → K) :
    Fintype.card κ ≤ Fintype.card ι + finrank K (LinearMap.ker (Matrix.of ε).mulVecLin) := by
  have h1 := (Matrix.of ε).mulVecLin.finrank_range_add_finrank_ker
  have h2 := (LinearMap.range (Matrix.of ε).mulVecLin).finrank_le
  rw [finrank_fintype_fun_eq_card] at h1 h2
  omega

/- English proof (translation)
Rewrite using `[LinearMap.mem_ker, funext_iff]`. Both sides reduce to the same expression.
-/
theorem mem_ker_mulVecLin_of (ε : ι → κ → K) (x : κ → K) :
    x ∈ LinearMap.ker (Matrix.of ε).mulVecLin ↔ ∀ a, ε a ⬝ᵥ x = 0 := by
  rw [LinearMap.mem_ker, funext_iff]; rfl

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Rewrite using `[← LinearMap.range_eq_top]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[finrank_fintype_fun_eq_card]`. Conclude with `LinearIndependent.rank_matrix (M := Matrix.of ε) hε`.
-/
theorem surjective_mulVecLin_of [Finite ι] {ε : ι → κ → K} (hε : LinearIndependent K ε) :
    Function.Surjective (Matrix.of ε).mulVecLin := by
  classical
  have := Fintype.ofFinite ι
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_fintype_fun_eq_card]
  exact LinearIndependent.rank_matrix (M := Matrix.of ε) hε

variable [DecidableEq κ]

/- English proof (translation)
Establish `: Finite ι` using `hε.finite`. Take `⟨e, he, he'⟩` from `exists_linearEquiv_comp_eq_and_apply_eq (surjective_mulVecLin_of hε) (surjective_mulVecLin_of hε') hφ hφ' (fun b => funext fun a => h a b) (fun b => funext fun a => h' a b)`. Set `g : GL κ K` to `Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e)`. Establish `hg (x) : vecAct g x = e x`. Simplify using `only [g, vecAct, Matrix.GeneralLinearGroup.toLin]`.

Conclude with `LinearMap.toMatrix'_mulVec e.toLinearMap x`. Use `⟨g, fun a => ?_, fun b => by rw [hg, he']⟩` and prove the remaining obligations. Use `dotProduct_eq _ _ fun y => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `e.surjective y`. Rewrite using `[← hg, covecAct_dotProduct_vecAct, hg]`.

Conclude with `(congrFun (he x) a).symm`.
-/
theorem exists_covecAct_eq_and_vecAct_eq {ε ε' : ι → κ → K} {φ φ' : ι' → κ → K}
    (hε : LinearIndependent K ε) (hε' : LinearIndependent K ε')
    (hφ : LinearIndependent K φ) (hφ' : LinearIndependent K φ')
    (h : ∀ a b, ε a ⬝ᵥ φ b = 0) (h' : ∀ a b, ε' a ⬝ᵥ φ' b = 0) :
    ∃ g : GL κ K, (∀ a, covecAct g (ε a) = ε' a) ∧ ∀ b, vecAct g (φ b) = φ' b := by
  have : Finite ι := hε.finite
  obtain ⟨e, he, he'⟩ := exists_linearEquiv_comp_eq_and_apply_eq (surjective_mulVecLin_of hε)
    (surjective_mulVecLin_of hε') hφ hφ' (fun b => funext fun a => h a b)
    (fun b => funext fun a => h' a b)
  let g : GL κ K := Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e)
  have hg (x) : vecAct g x = e x := by
    simp only [g, vecAct, Matrix.GeneralLinearGroup.toLin]
    exact LinearMap.toMatrix'_mulVec e.toLinearMap x
  refine ⟨g, fun a => ?_, fun b => by rw [hg, he']⟩
  refine dotProduct_eq _ _ fun y => ?_
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← hg, covecAct_dotProduct_vecAct, hg]
  exact (congrFun (he x) a).symm

omit [DecidableEq κ] in

/- English proof (translation)
Establish `h1` using `card_le_card_add_finrank_ker φ`. Rewrite `h1` using `[Fintype.card_fin]`. Take `⟨ε', hε', hm, hf⟩` from `exists_linearIndependent_flag_mem (LinearMap.ker (Matrix.of φ).mulVecLin) (by omega) ε fun a => (mem_ker_mulVecLin_of _ _).mpr fun b => by rw [dotProduct_comm, h]`. Establish `h2` using `card_le_card_add_finrank_ker ε'`. Rewrite `h2` using `[Fintype.card_fin]`.

Take `⟨φ', hφ', hm', hf'⟩` from `exists_linearIndependent_flag_mem (LinearMap.ker (Matrix.of ε').mulVecLin) (by omega) φ fun b => (mem_ker_mulVecLin_of _ _).mpr fun a => by`. Rewrite using `[dotProduct_comm]`. Conclude with `(mem_ker_mulVecLin_of _ _).mp (hm a) b`. Conclude with `⟨ε', φ', hε', hφ', fun a b => (mem_ker_mulVecLin_of _ _).mp (hm' b) a, hf, hf'⟩`.
-/
theorem exists_linearIndependent_perp_flag {p q : ℕ} (hpq : p + q ≤ Fintype.card κ)
    (ε : Fin p → κ → K) (φ : Fin q → κ → K) (h : ∀ a b, ε a ⬝ᵥ φ b = 0) :
    ∃ (ε' : Fin p → κ → K) (φ' : Fin q → κ → K), LinearIndependent K ε' ∧
      LinearIndependent K φ' ∧ (∀ a b, ε' a ⬝ᵥ φ' b = 0) ∧
      (∀ a, ε a ∈ Submodule.span K (ε' '' Set.Iic a)) ∧
      ∀ b, φ b ∈ Submodule.span K (φ' '' Set.Iic b) := by
  have h1 := card_le_card_add_finrank_ker φ
  rw [Fintype.card_fin] at h1
  obtain ⟨ε', hε', hm, hf⟩ := exists_linearIndependent_flag_mem
    (LinearMap.ker (Matrix.of φ).mulVecLin) (by omega) ε
    fun a => (mem_ker_mulVecLin_of _ _).mpr fun b => by rw [dotProduct_comm, h]
  have h2 := card_le_card_add_finrank_ker ε'
  rw [Fintype.card_fin] at h2
  obtain ⟨φ', hφ', hm', hf'⟩ := exists_linearIndependent_flag_mem
    (LinearMap.ker (Matrix.of ε').mulVecLin) (by omega) φ
    fun b => (mem_ker_mulVecLin_of _ _).mpr fun a => by
      rw [dotProduct_comm]; exact (mem_ker_mulVecLin_of _ _).mp (hm a) b
  exact ⟨ε', φ', hε', hφ', fun a b => (mem_ker_mulVecLin_of _ _).mp (hm' b) a, hf, hf'⟩

end Transitive

section Flag

variable {R : Type*} [CommRing R] {T κ : Type*} {p q : ℕ} [Fintype κ]

/- English proof (translation)
Use `choose c hc using fun b => (Submodule.mem_span_range_iff_exists_fun R).mp (h b)`. Use `⟨(Matrix.of c).det, ?_⟩` and prove the remaining obligations. Establish `: (Matrix.of fun a b => L a (v b)) = (Matrix.of fun a b => L a (w b)) * ((algebraMap R A).mapMatrix (Matrix.of c))ᵀ`. Use extensionality with `a b`. Simplify using `[← hc b, Matrix.mul_apply, Algebra.smul_def, mul_comm]`.

Rewrite using `[this, det_mul, det_transpose, ← RingHom.map_det, Algebra.smul_def, mul_comm]`.
-/
theorem exists_det_eq_smul_of_mem_span {A M ι : Type*} [CommRing A] [Algebra R A] [AddCommGroup M]
    [Module R M] [Fintype ι] [DecidableEq ι] (L : ι → M →ₗ[R] A) (v w : ι → M)
    (h : ∀ b, v b ∈ Submodule.span R (Set.range w)) :
    ∃ r : R, (Matrix.of fun a b => L a (v b)).det = r • (Matrix.of fun a b => L a (w b)).det := by
  choose c hc using fun b => (Submodule.mem_span_range_iff_exists_fun R).mp (h b)
  refine ⟨(Matrix.of c).det, ?_⟩
  have : (Matrix.of fun a b => L a (v b)) =
      (Matrix.of fun a b => L a (w b)) * ((algebraMap R A).mapMatrix (Matrix.of c))ᵀ := by
    ext a b
    simp [← hc b, Matrix.mul_apply, Algebra.smul_def, mul_comm]
  rw [this, det_mul, det_transpose, ← RingHom.map_det, Algebra.smul_def, mul_comm]

/- English proof (translation)
Use `Submodule.span_mono ?_ (h _)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `⟨⟨a.val, lt_of_le_of_lt (Fin.le_def.mp ha) b.isLt⟩, rfl⟩`.
-/
theorem mem_span_range_lead {M : Type*} [AddCommGroup M] [Module R M] {m : ℕ} {v w : Fin m → M}
    (h : ∀ b, v b ∈ Submodule.span R (w '' Set.Iic b)) (i : Fin m) (b : Fin (i.val + 1)) :
    v (lead i b) ∈ Submodule.span R (Set.range fun a => w (lead i a)) := by
  refine Submodule.span_mono ?_ (h _)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨⟨a.val, lt_of_le_of_lt (Fin.le_def.mp ha) b.isLt⟩, rfl⟩

/- English proof (translation)
The claim follows from `exists_det_eq_smul_of_mem_span (A := Poly R T p q κ) (fun a => xForm t (lead i a)) (fun b => ε (lead i b)) (fun b => ε' (lead i b)) (mem_span_range_lead h i)`.
-/
theorem exists_xMinor_eq_smul (t : T) (i : Fin p) {ε ε' : Fin p → κ → R}
    (h : ∀ a, ε a ∈ Submodule.span R (ε' '' Set.Iic a)) :
    ∃ r : R, (xMinor t i ε : Poly R T p q κ) = r • xMinor t i ε' :=
  exists_det_eq_smul_of_mem_span (A := Poly R T p q κ) (fun a => xForm t (lead i a)) (fun b => ε (lead i b))
    (fun b => ε' (lead i b)) (mem_span_range_lead h i)

/- English proof (translation)
The claim follows from `exists_det_eq_smul_of_mem_span (A := Poly R T p q κ) (fun a => yForm t (lead i a)) (fun b => φ (lead i b)) (fun b => φ' (lead i b)) (mem_span_range_lead h i)`.
-/
theorem exists_yMinor_eq_smul (t : T) (i : Fin q) {φ φ' : Fin q → κ → R}
    (h : ∀ b, φ b ∈ Submodule.span R (φ' '' Set.Iic b)) :
    ∃ r : R, (yMinor t i φ : Poly R T p q κ) = r • yMinor t i φ' :=
  exists_det_eq_smul_of_mem_span (A := Poly R T p q κ) (fun a => yForm t (lead i a)) (fun b => φ (lead i b))
    (fun b => φ' (lead i b)) (mem_span_range_lead h i)

/- English proof (translation)
Use `choose r hr using fun t i => exists_xMinor_eq_smul (q := q) t i (hε t)`. Use `choose s hs using fun t i => exists_yMinor_eq_smul (p := p) t i (hφ t)`. Use `⟨∏ t, ((∏ i, r t i ^ c t i) * ∏ i, s t i ^ c' t i), ?_⟩` and prove the remaining obligations. Simplify using `only [minorProd, hr, hs, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, map_prod, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_minorProd_eq_smul [Fintype T] (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)
    {ε ε' : T → Fin p → κ → R} {φ φ' : T → Fin q → κ → R}
    (hε : ∀ t a, ε t a ∈ Submodule.span R (ε' t '' Set.Iic a))
    (hφ : ∀ t b, φ t b ∈ Submodule.span R (φ' t '' Set.Iic b)) :
    ∃ r : R, minorProd c c' ε φ = r • minorProd c c' ε' φ' := by
  choose r hr using fun t i => exists_xMinor_eq_smul (q := q) t i (hε t)
  choose s hs using fun t i => exists_yMinor_eq_smul (p := p) t i (hφ t)
  refine ⟨∏ t, ((∏ i, r t i ^ c t i) * ∏ i, s t i ^ c' t i), ?_⟩
  simp only [minorProd, hr, hs, smul_eq_C_mul, mul_pow, Finset.prod_mul_distrib, map_prod, map_mul,
    map_pow]
  ring

end Flag

section Span

variable {K : Type*} [Field K] {T κ : Type*} [Fintype T] {p q n : ℕ}

omit [Fintype T] in

/- English proof (translation)
Use `choose g hg hg' using fun t => exists_covecAct_eq_and_vecAct_eq (hε t) (hε' t) (hφ t) (hφ' t) (h t) (h' t)`. Conclude with `⟨g, hg, hg'⟩`.
-/
theorem exists_act_eq_of_isPerp [Fintype κ] [DecidableEq κ] {ε ε' : T → Fin p → κ → K}
    {φ φ' : T → Fin q → κ → K}
    (hε : ∀ t, LinearIndependent K (ε t)) (hε' : ∀ t, LinearIndependent K (ε' t))
    (hφ : ∀ t, LinearIndependent K (φ t)) (hφ' : ∀ t, LinearIndependent K (φ' t))
    (h : IsPerp ε φ) (h' : IsPerp ε' φ') :
    ∃ g : T → GL κ K, (∀ t a, covecAct (g t) (ε t a) = ε' t a) ∧
      ∀ t b, vecAct (g t) (φ t b) = φ' t b := by
  choose g hg hg' using fun t =>
    exists_covecAct_eq_and_vecAct_eq (hε t) (hε' t) (hφ t) (hφ' t) (h t) (h' t)
  exact ⟨g, hg, hg'⟩

/- English proof (translation)
Take `⟨g, hg, hg'⟩` from `exists_act_eq_of_isPerp hε hε' hφ hφ' h h'`. Conclude with `⟨g, by simp only [colAct_minorProd, hg, hg']⟩`.
-/
theorem exists_colAct_minorProd_eq [Fintype κ] [DecidableEq κ] (c : T → Fin p → ℕ)
    (c' : T → Fin q → ℕ) {ε ε' : T → Fin p → κ → K} {φ φ' : T → Fin q → κ → K}
    (hε : ∀ t, LinearIndependent K (ε t)) (hε' : ∀ t, LinearIndependent K (ε' t))
    (hφ : ∀ t, LinearIndependent K (φ t)) (hφ' : ∀ t, LinearIndependent K (φ' t))
    (h : IsPerp ε φ) (h' : IsPerp ε' φ') :
    ∃ g : T → GL κ K, colAct K T p q κ g (minorProd c c' ε φ) = minorProd c c' ε' φ' := by
  obtain ⟨g, hg, hg'⟩ := exists_act_eq_of_isPerp hε hε' hφ hφ' h h'
  exact ⟨g, by simp only [colAct_minorProd, hg, hg']⟩

/- English proof (translation)
Use `choose ε' φ' h1 h2 h3 h4 h5 using fun t => exists_linearIndependent_perp_flag hpq (ε t) (φ t) (h t)`. Take `⟨r, hr⟩` from `Harm.exists_minorProd_eq_smul c c' h4 h5`. Conclude with `⟨r, ε', φ', h1, h2, h3, hr⟩`.
-/
theorem IsPerp.exists_minorProd_eq_smul [Fintype κ] (hpq : p + q ≤ Fintype.card κ)
    (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ) {ε : T → Fin p → κ → K} {φ : T → Fin q → κ → K}
    (h : IsPerp ε φ) :
    ∃ (r : K) (ε' : T → Fin p → κ → K) (φ' : T → Fin q → κ → K),
      (∀ t, LinearIndependent K (ε' t)) ∧ (∀ t, LinearIndependent K (φ' t)) ∧ IsPerp ε' φ' ∧
      minorProd c c' ε φ = r • minorProd c c' ε' φ' := by
  choose ε' φ' h1 h2 h3 h4 h5 using fun t =>
    exists_linearIndependent_perp_flag hpq (ε t) (φ t) (h t)
  obtain ⟨r, hr⟩ := Harm.exists_minorProd_eq_smul c c' h4 h5
  exact ⟨r, ε', φ', h1, h2, h3, hr⟩

variable (h : p + q ≤ n) (c : T → Fin p → ℕ) (c' : T → Fin q → ℕ)

/- English proof (translation)
The claim follows from `exists_colAct_minorProd_eq c c' (fun _ => linearIndependent_baseCovec h) hε (fun _ => linearIndependent_baseVec h) hφ (isPerp_base K T h) hp`.
-/
theorem exists_colAct_basePoly_eq {ε : T → Fin p → Fin n → K} {φ : T → Fin q → Fin n → K}
    (hε : ∀ t, LinearIndependent K (ε t)) (hφ : ∀ t, LinearIndependent K (φ t))
    (hp : IsPerp ε φ) :
    ∃ g : T → GL (Fin n) K, colAct K T p q (Fin n) g (basePoly K h c c') = minorProd c c' ε φ :=
  exists_colAct_minorProd_eq c c' (fun _ => linearIndependent_baseCovec h) hε
    (fun _ => linearIndependent_baseVec h) hφ (isPerp_base K T h) hp

/- English proof (translation)
Take `⟨r, ε', φ', h1, h2, h3, h4⟩` from `hp.exists_minorProd_eq_smul (by simpa using h) c c'`. Take `⟨g, hg⟩` from `exists_colAct_basePoly_eq h c c' h1 h2 h3`. Conclude with `⟨r, g, by rw [h4, hg]⟩`.
-/
theorem exists_minorProd_eq_smul_colAct_basePoly {ε : T → Fin p → Fin n → K}
    {φ : T → Fin q → Fin n → K} (hp : IsPerp ε φ) :
    ∃ (r : K) (g : T → GL (Fin n) K),
      minorProd c c' ε φ = r • colAct K T p q (Fin n) g (basePoly K h c c') := by
  obtain ⟨r, ε', φ', h1, h2, h3, h4⟩ := hp.exists_minorProd_eq_smul (by simpa using h) c c'
  obtain ⟨g, hg⟩ := exists_colAct_basePoly_eq h c c' h1 h2 h3
  exact ⟨r, g, by rw [h4, hg]⟩

/- English proof (translation)
Take `⟨r, g, e⟩` from `exists_minorProd_eq_smul_colAct_basePoly h c c' hp`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (colAct_basePoly_mem h c c' g)`.
-/
theorem minorProd_mem_orbitSpan {ε : T → Fin p → Fin n → K} {φ : T → Fin q → Fin n → K}
    (hp : IsPerp ε φ) : minorProd c c' ε φ ∈ orbitSpan K h c c' := by
  obtain ⟨r, g, e⟩ := exists_minorProd_eq_smul_colAct_basePoly h c c' hp
  rw [e]
  exact Submodule.smul_mem _ _ (colAct_basePoly_mem h c c' g)

/- English proof (translation)
Use `hε.map' (Matrix.vecMulLinear ((g⁻¹ : GL κ R) : Matrix κ κ R)) ?_` and prove the remaining obligations. Rewrite using `[LinearMap.ker_eq_bot]`. Conclude with `Matrix.vecMul_injective_of_isUnit (Units.isUnit _)`.
-/
theorem linearIndependent_covecAct {R ι : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]
    (g : GL κ R) {ε : ι → κ → R} (hε : LinearIndependent R ε) :
    LinearIndependent R fun a => covecAct g (ε a) := by
  refine hε.map' (Matrix.vecMulLinear ((g⁻¹ : GL κ R) : Matrix κ κ R)) ?_
  rw [LinearMap.ker_eq_bot]
  exact Matrix.vecMul_injective_of_isUnit (Units.isUnit _)

/- English proof (translation)
Use `hφ.map' (Matrix.mulVecLin (g : Matrix κ κ R)) ?_` and prove the remaining obligations. Rewrite using `[LinearMap.ker_eq_bot]`. Conclude with `Matrix.mulVec_injective_of_isUnit (Units.isUnit _)`.
-/
theorem linearIndependent_vecAct {R ι : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]
    (g : GL κ R) {φ : ι → κ → R} (hφ : LinearIndependent R φ) :
    LinearIndependent R fun b => vecAct g (φ b) := by
  refine hφ.map' (Matrix.mulVecLin (g : Matrix κ κ R)) ?_
  rw [LinearMap.ker_eq_bot]
  exact Matrix.mulVec_injective_of_isUnit (Units.isUnit _)

/- English proof (translation)
Use extensionality with `P`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Conclude with `⟨_, _, fun t => linearIndependent_covecAct (g t) (linearIndependent_baseCovec h), fun t => linearIndependent_vecAct (g t) (linearIndependent_baseVec h), (isPerp_base K T h).act g, colAct_minorProd g c c' _ _⟩`. Introduce and unpack `⟨ε, φ, h1, h2, h3, rfl⟩`.

Conclude with `exists_colAct_basePoly_eq h c c' h1 h2 h3`.
-/
theorem range_colAct_basePoly :
    (Set.range fun g : T → GL (Fin n) K => colAct K T p q (Fin n) g (basePoly K h c c')) =
      {P | ∃ (ε : T → Fin p → Fin n → K) (φ : T → Fin q → Fin n → K),
        (∀ t, LinearIndependent K (ε t)) ∧ (∀ t, LinearIndependent K (φ t)) ∧ IsPerp ε φ ∧
        P = minorProd c c' ε φ} := by
  ext P
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨_, _, fun t => linearIndependent_covecAct (g t) (linearIndependent_baseCovec h),
      fun t => linearIndependent_vecAct (g t) (linearIndependent_baseVec h),
      (isPerp_base K T h).act g, colAct_minorProd g c c' _ _⟩
  · rintro ⟨ε, φ, h1, h2, h3, rfl⟩
    exact exists_colAct_basePoly_eq h c c' h1 h2 h3

/- English proof (translation)
Rewrite using `[orbitSpan, range_colAct_basePoly]`.
-/
theorem orbitSpan_eq_span_linearIndependent :
    orbitSpan K h c c' = Submodule.span K
      {P | ∃ (ε : T → Fin p → Fin n → K) (φ : T → Fin q → Fin n → K),
        (∀ t, LinearIndependent K (ε t)) ∧ (∀ t, LinearIndependent K (φ t)) ∧ IsPerp ε φ ∧
        P = minorProd c c' ε φ} := by
  rw [orbitSpan, range_colAct_basePoly]

end Span

end GlobalTheory.Harm
