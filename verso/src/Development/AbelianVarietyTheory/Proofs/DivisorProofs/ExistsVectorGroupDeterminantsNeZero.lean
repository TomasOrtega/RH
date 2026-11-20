import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericGroupDet

/- English proof (translation)
Establish `: (Matrix.of fun h g : S => f (h * g)) = (Equiv.inv S).permMatrix ℂ`. Use extensionality with `h g`. Simplify using `[Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hf, mul_eq_one_iff_inv_eq]`. Rewrite using `[this, Matrix.det_permutation]`. Simplify using the standard rewrite rules.
-/
theorem det_delta_ne_zero (S : Type) [Group S] [Fintype S] [DecidableEq S] (f : S → ℂ)
    (hf : ∀ h, f h = if h = 1 then 1 else 0) :
    (Matrix.of fun h g : S => f (h * g)).det ≠ 0 := by
  have : (Matrix.of fun h g : S => f (h * g)) = (Equiv.inv S).permMatrix ℂ := by
    ext h g
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hf, mul_eq_one_iff_inv_eq]
  rw [this, Matrix.det_permutation]
  simp

/- English proof (translation)
Use `set s : Set (J → ℂ) := (fun v => fun j => ev v (r j)) '' (W : Set V) with hs`. Establish `htop : Submodule.span ℂ s = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨φ, hφ0, hle⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)`. Establish `hφ : ∀ x : J → ℂ, φ x = ∑ j, x j * φ (fun j' => if j = j' then 1 else 0)` using `fun x => by`.

Rewrite using `[LinearMap.pi_apply_eq_sum_univ φ x]`. Simplify using `[smul_eq_mul]`. Establish `ha` using `h3 (fun j => φ (fun j' => if j = j' then 1 else 0)) fun v hv => by`. Use `hle (Submodule.subset_span ⟨v, hv, rfl⟩)` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, hφ]`.

Simplify `this` using `[mul_comm]`. Apply `hφ0` to reduce the goal to its premises. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[hφ x, LinearMap.zero_apply]`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [congrFun ha j]; simp`.

Set `b : J → ℂ` to `fun j => if r j = 1 then 1 else 0`. Establish `hb : b ∈ Submodule.span ℂ s` using `htop ▸ Submodule.mem_top`. Take `⟨n, c, g, hg⟩` from `Submodule.mem_span_set'.1 hb`. Use `choose w hw hwg using fun k => (g k).2`. Use `⟨n, c, w, hw, fun h => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hr : h ∈ Set.range r`. Take `⟨j, rfl⟩` from `hr`. Use `congrFun hg j` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b] at this`. Rewrite using `[← this]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← hwg k]`. Establish `h1' : h ≠ 1`. Introduce and unpack `rfl`. Take `⟨j, hj⟩` from `h1`.

Conclude with `hr ⟨j, hj⟩`. Rewrite using `[if_neg h1']`. Conclude with `Finset.sum_eq_zero fun k _ => by rw [h2 _ (hw k) h hr, mul_zero]`.
-/
theorem exists_combination_delta (F V S J : Type) [Field F] [Algebra F ℂ] [AddCommGroup V] [Module F V]
    [Group S] [Fintype S] [DecidableEq S] [Fintype J]
    (ev : V →ₗ[F] (S → ℂ)) (r : J → S) (W : Submodule F V) (h1 : ∃ j, r j = 1)
    (h2 : ∀ v ∈ W, ∀ h, h ∉ Set.range r → ev v h = 0)
    (h3 : ∀ a : J → ℂ, (∀ v ∈ W, ∑ j, a j * ev v (r j) = 0) → a = 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → V), (∀ k, w k ∈ W) ∧
      ∀ h, ∑ k, c k * ev (w k) h = if h = 1 then 1 else 0 := by
  classical
  set s : Set (J → ℂ) := (fun v => fun j => ev v (r j)) '' (W : Set V) with hs
  have htop : Submodule.span ℂ s = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφ : ∀ x : J → ℂ, φ x = ∑ j, x j * φ (fun j' => if j = j' then 1 else 0) := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp [smul_eq_mul]
    have ha := h3 (fun j => φ (fun j' => if j = j' then 1 else 0)) fun v hv => by
      have := hle (Submodule.subset_span ⟨v, hv, rfl⟩)
      rw [LinearMap.mem_ker, hφ] at this
      simpa [mul_comm] using this
    apply hφ0
    refine LinearMap.ext fun x => ?_
    rw [hφ x, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [congrFun ha j]; simp
  let b : J → ℂ := fun j => if r j = 1 then 1 else 0
  have hb : b ∈ Submodule.span ℂ s := htop ▸ Submodule.mem_top
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hb
  choose w hw hwg using fun k => (g k).2
  refine ⟨n, c, w, hw, fun h => ?_⟩
  by_cases hr : h ∈ Set.range r
  · obtain ⟨j, rfl⟩ := hr
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hwg k]
  · have h1' : h ≠ 1 := by
      rintro rfl
      obtain ⟨j, hj⟩ := h1
      exact hr ⟨j, hj⟩
    rw [if_neg h1']
    exact Finset.sum_eq_zero fun k _ => by rw [h2 _ (hw k) h hr, mul_zero]

/- English proof (translation)
Use `Fintype.ofFinite ι` as an intermediate fact. Use `choose n c w hw hcw using fun i => exists_combination_delta F V S (J i) (ev i) (r i) (W i) (h1 i) (h2 i) (h3 i)`. Set `vec : (Σ i, Fin (n i)) → V` to `fun p => w p.1 p.2`. Set `P : ι → MvPolynomial (Σ i, Fin (n i)) ℂ` to `fun i => Matrix.det (Matrix.of fun h g : S => ∑ p, MvPolynomial.X p * MvPolynomial.C (ev i (vec p) (h * g)))`. Establish `hP : ∀ i (x : (Σ i, Fin (n i)) → ℂ), MvPolynomial.eval x (P i) = (Matrix.of fun h g : S => ∑ p, x p * ev i (vec p) (h * g)).det`.

Introduce `i x`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `h g`. Simplify using `[RingHom.mapMatrix_apply]`.

Establish `hPi : ∀ i, P i ≠ 0`. Introduce `i hz`. Set `x : (Σ i, Fin (n i)) → ℂ` to `fun p => if p.1 = i then c p.1 p.2 else 0`. Establish `hx : ∀ h, ∑ p, x p * ev i (vec p) h = if h = 1 then 1 else 0`. Introduce `h`.

Rewrite using `[← hcw i h, Fintype.sum_sigma, Finset.sum_eq_single i]`. Simplify using `[x, vec]`. Introduce `b _ hb`. Conclude with `Finset.sum_eq_zero fun k _ => by simp [x, hb]`. Simplify using the standard rewrite rules.

Use `det_delta_ne_zero S _ hx` as an intermediate fact. Rewrite `this` using `[← hP, hz, map_zero]`. Conclude with `this rfl`. Establish `hQ : (∏ i, P i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hPi i`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx, hQx⟩ : ∃ x ∈ Set.pi Set.univ (fun _ : (Σ i, Fin (n i)) => Set.range (algebraMap F ℂ)), MvPolynomial.eval x (∏ i, P i) ≠ 0 := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `hQ (MvPolynomial.funext_set (fun _ => Set.range (algebraMap F ℂ)) (fun _ => Set.infinite_range_of_injective (algebraMap F ℂ).injective) fun x hx => by rw [hcon x hx, map_zero])`. Use `choose t ht using fun p => hx p (Set.mem_univ p)`. Use `⟨∑ p, t p • vec p, fun i => ?_⟩` and prove the remaining obligations.

Establish `hne : MvPolynomial.eval x (P i) ≠ 0`. Rewrite `hQx` using `[map_prod]`. Conclude with `Finset.prod_ne_zero_iff.1 hQx i (Finset.mem_univ _)`. Rewrite `hne` using `[hP]`. Use `hne using 2` and compare the differences between its conclusion and the goal.

Use extensionality with `h g`. Simplify using `[map_sum, Finset.sum_apply, Algebra.smul_def, ht]`.
-/
theorem exists_vec_det_ne_zero (F : Type) [Field F] [CharZero F] [Algebra F ℂ] (V : Type) [AddCommGroup V] [Module F V]
    (S : Type) [Group S] [Fintype S] [DecidableEq S] (ι : Type) [Finite ι] (ev : ι → V →ₗ[F] (S → ℂ))
    (J : ι → Type) [∀ i, Fintype (J i)] (r : ∀ i, J i → S) (W : ι → Submodule F V)
    (h1 : ∀ i, ∃ j, r i j = 1) (h2 : ∀ i, ∀ v ∈ W i, ∀ h, h ∉ Set.range (r i) → ev i v h = 0)
    (h3 : ∀ i (a : J i → ℂ), (∀ v ∈ W i, ∑ j, a j * ev i v (r i j) = 0) → a = 0) :
    ∃ v : V, ∀ i, (Matrix.of fun h g : S => ev i v (h * g)).det ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  choose n c w hw hcw using fun i => exists_combination_delta F V S (J i) (ev i) (r i) (W i) (h1 i) (h2 i) (h3 i)
  let vec : (Σ i, Fin (n i)) → V := fun p => w p.1 p.2
  let P : ι → MvPolynomial (Σ i, Fin (n i)) ℂ := fun i =>
    Matrix.det (Matrix.of fun h g : S => ∑ p, MvPolynomial.X p * MvPolynomial.C (ev i (vec p) (h * g)))
  have hP : ∀ i (x : (Σ i, Fin (n i)) → ℂ), MvPolynomial.eval x (P i) =
      (Matrix.of fun h g : S => ∑ p, x p * ev i (vec p) (h * g)).det := by
    intro i x
    rw [RingHom.map_det]
    congr 1
    ext h g
    simp [RingHom.mapMatrix_apply]
  have hPi : ∀ i, P i ≠ 0 := by
    intro i hz
    let x : (Σ i, Fin (n i)) → ℂ := fun p => if p.1 = i then c p.1 p.2 else 0
    have hx : ∀ h, ∑ p, x p * ev i (vec p) h = if h = 1 then 1 else 0 := by
      intro h
      rw [← hcw i h, Fintype.sum_sigma, Finset.sum_eq_single i]
      · simp [x, vec]
      · intro b _ hb
        exact Finset.sum_eq_zero fun k _ => by simp [x, hb]
      · simp
    have := det_delta_ne_zero S _ hx
    rw [← hP, hz, map_zero] at this
    exact this rfl
  have hQ : (∏ i, P i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hPi i
  obtain ⟨x, hx, hQx⟩ : ∃ x ∈ Set.pi Set.univ (fun _ : (Σ i, Fin (n i)) => Set.range (algebraMap F ℂ)),
      MvPolynomial.eval x (∏ i, P i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ (MvPolynomial.funext_set (fun _ => Set.range (algebraMap F ℂ))
      (fun _ => Set.infinite_range_of_injective (algebraMap F ℂ).injective)
      fun x hx => by rw [hcon x hx, map_zero])
  choose t ht using fun p => hx p (Set.mem_univ p)
  refine ⟨∑ p, t p • vec p, fun i => ?_⟩
  have hne : MvPolynomial.eval x (P i) ≠ 0 := by
    rw [map_prod] at hQx
    exact Finset.prod_ne_zero_iff.1 hQx i (Finset.mem_univ _)
  rw [hP] at hne
  convert hne using 2
  ext h g
  simp [map_sum, Finset.sum_apply, Algebra.smul_def, ht]

end GlobalTheory.GenericGroupDet
